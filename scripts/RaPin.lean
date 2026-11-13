/-! RA-pin self-audit helper (NOT part of the release tree; driven by scripts/check-ra-pin, which prepends the imports).

BRIEF "RETURN-ADDRESS PIN GAP": a row precondition can constrain the caller's return address (amd64: the word [RSP];
arm64: X30) and no Janus release's audit catches every spelling. This tool takes a row theorem, finds every Janus main-theorem
form in its statement (any Janus constant with a binder named `pre`: Ensures, EnsuresWithin, EnsuresGo/GoX,
RunsAtLeastOnCall, ...), applies `pre` to a fresh state `s`, unfolds EVERY definition/structure of the fv-modexp package
(modules `FvModexp.*`), keeps framework/dependency constants folded, flattens ∧ / ∃ / ∀ / → / let, and classifies the
conjuncts against the probe forms of /srv/janus-ops/v033/probe/{RspBypass64,LrPin}.lean:

  FLAG (must be read by the auditor; any FLAG fails the check):
    X30          arm64: the conjunct mentions `s.regs 30` (LrPin e1/e2)
    RA-READ      a Memory access (readLE / bytes / any function of a Memory) at an address that mentions RSP or an
                 RSP alias, other than `RSP + k` with a literal k ≥ 8 (d0, c1, c2, c3, c6, c7)
    (c4, `Memory.bytes` at RSP + i, is an RA-READ; other byte reads are INFO BYTES)
    MEM-EQ       an equation between Memory / State values, or function values mentioning the state (c8)
    RSP-PIN      RSP equated to, or bounded on both sides by, closed terms (c5) — then every closed-address read is listed
    CONST-READ   a closed-address Memory read while RSP is pinned (c5)
    OPAQUE       a fv-modexp constant that could not be unfolded (opaque / inductive Prop) applied to state terms
  INFO (listed for completeness, not failing):
    STACK-ARG    a read at `RSP + k`, k ≥ 8 literal (stack arguments / caller frame; allowed)
    RSP-REL      any other conjunct mentioning RSP (window bounds, Outside/Apart/Held with RSP, alignment ...)
    FRAMEWORK    distinct non-fv-modexp heads of conjuncts applied to the state (ABI predicates: check they are Janus's)
An "RSP alias" is a variable (theorem binder or ∃/∀/let-bound) equated with an RSP term, or bounded by RSP terms on both
sides (fixpoint). Over-approximating on purpose: every FLAG is a line for the manual audit, not a verdict. -/

open Lean Meta Elab Command

namespace RaPin

def ownPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`FvModexp).isPrefixOf (env.header.moduleNames[i.toNat]!)
  | none => true   -- declared in the current (generated) file: treat as project code

/-- Unfold project definitions at the head (and beta / zeta), with fuel. -/
partial def unfoldHead (e : Expr) (fuel : Nat := 200) : MetaM Expr := do
  if fuel = 0 then return e
  let e := e.headBeta
  match e with
  | .letE _ _ v b _ => unfoldHead (b.instantiate1 v) (fuel - 1)
  | .mdata _ b => unfoldHead b (fuel - 1)
  | _ =>
    let env ← getEnv
    match e.getAppFn with
    | .const n us =>
      if ownPkg env n then
        match env.find? n with
        | some (.defnInfo d) =>
          let v := d.value.instantiateLevelParams d.levelParams us
          unfoldHead (v.beta e.getAppArgs) (fuel - 1)
        | some (.thmInfo _) => return e
        | _ => return e
      else return e
    | _ => return e

/-- Deep unfolding of project definitions everywhere (structures stay; see `expandStruct`). -/
def deepUnfold (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let step (e : Expr) : MetaM TransformStep := do
    match e.getAppFn with
    | .const n _ =>
      if ownPkg env n then
        if let some (.defnInfo _) := env.find? n then
          return .visit (← unfoldHead e 50)
      return .continue
    | .letE .. => return .visit (← unfoldHead e 5)
    | _ => return .continue
  Meta.transform e (pre := step)

/-- A project structure (Prop) at the head: its fields as conjuncts. -/
def expandStruct (e : Expr) : MetaM (Option (Array Expr)) := do
  let env ← getEnv
  let .const n us := e.getAppFn | return none
  unless ownPkg env n do return none
  let some (.inductInfo iv) := env.find? n | return none
  unless isStructure env n do return none
  let some ci := getStructureInfo? env n | return none
  let _ := ci
  let ctor := getStructureCtor env n
  let ty := ctor.type.instantiateLevelParams ctor.levelParams us
  let args := e.getAppArgs
  if args.size < iv.numParams then return none
  let ty ← instantiateForall ty (args.extract 0 iv.numParams)
  forallTelescopeReducing ty fun xs _ => do
    let mut out := #[]
    for x in xs do out := out.push (← inferType x)
    return some out

structure Item where
  ctx : String
  e : Expr

/-- Flatten ∧ / ∃ / ∀ / → / let; keeps the fvars of ∃/∀ binders alive in the returned items (they live in the
caller's `withLocalDecl` scope, so this runs in CPS). -/
partial def collect (e : Expr) (ctx : String) (k : Array Item → MetaM α) : MetaM α := do
  let e ← unfoldHead e
  if let some fs ← expandStruct e then
    return ← collectAll fs.toList ctx #[] k
  match e.getAppFnArgs with
  | (``And, #[a, b]) => collectAll [a, b] ctx #[] k
  | (``Exists, #[ty, .lam n _ b bi]) =>
    withLocalDecl n bi ty fun x => collect (b.instantiate1 x) s!"{ctx}∃{n}." k
  | (``Exists, #[ty, f]) =>
    withLocalDeclD `x ty fun x => collect (mkApp f x) s!"{ctx}∃x." k
  | _ =>
    match e with
    | .forallE n ty b bi =>
      if b.hasLooseBVars then
        withLocalDecl n bi ty fun x => collect (b.instantiate1 x) s!"{ctx}∀{n}." k
      else
        collect ty s!"{ctx}(premise)" fun xs => collect b s!"{ctx}(⇒)" fun ys => k (xs ++ ys)
    | _ => k #[⟨ctx, e⟩]
where
  collectAll (es : List Expr) (ctx : String) (acc : Array Item) (k : Array Item → MetaM α) : MetaM α :=
    match es with
    | [] => k acc
    | e :: rest => collect e ctx fun xs => collectAll rest ctx (acc ++ xs) k

def regIdx? (e : Expr) : MetaM (Option (Name × Nat)) := do
  -- `State.regs s i` (projection-function application or `.proj` form)
  let f := e.getAppFn
  let args := e.getAppArgs
  let nm? : Option Name := match f with
    | .const n _ => if n.getString! == "regs" then some n else none
    | .proj sn 0 _ => if sn.getString! == "State" then some (sn ++ `regs) else none
    | _ => none
  let some nm := nm? | return none
  let idx? := match f with | .proj .. => args[0]? | _ => args[1]?
  let some idx := idx? | return none
  let some i ← (do
      if let some i ← evalNat idx then pure (some i) else
      evalNat (← whnf idx)) | return none
  return some (nm, i)

/-- Does `e` mention the return-address register (amd64 RSP = regs 4 / arm64 X30 = regs 30)? -/
def mentionsReg (target : Nat) (e : Expr) : MetaM Bool := do
  let r ← IO.mkRef false
  let _ ← Meta.transform e (pre := fun t => do
    if ← r.get then return .done t
    if let some (_, i) ← regIdx? t then
      if i == target then r.set true; return .done t
    return .continue)
  r.get

def closedTerm (e : Expr) : Bool := !e.hasFVar && !e.hasMVar

def mentionsAny (fs : Array FVarId) (e : Expr) : Bool := fs.any fun f => e.containsFVar f

def isAliasy (target : Nat) (taint : Array FVarId) (e : Expr) : MetaM Bool := do
  if mentionsAny taint e then return true
  mentionsReg target e


/-- `(s.regs 4).toNat + k` with literal `k ≥ 8`. -/
def stackArg? (target : Nat) (a : Expr) : MetaM (Option Nat) := do
  match a.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, k]) =>
    match ← evalNat k with
    | some kv =>
      if kv ≥ 8 then
        match x.getAppFnArgs with
        | (``BitVec.toNat, #[_, r]) =>
          if let some (_, i) ← regIdx? r then if i == target then return some kv
          return none
        | _ => return none
      else return none
    | none => return none
  | _ => return none

def isMemTy (t : Expr) : Bool :=
  match t.getAppFn with
  | .const n _ => n.getString! == "Memory"
  | _ => false

def isStateTy (t : Expr) : Bool :=
  match t.getAppFn with
  | .const n _ => n.getString! == "Memory" || n.getString! == "State"
  | _ => false

/-- Strip `BitVec.toNat`, `BitVec.ofNat`, and `+ c` / `- c` / `c +` with closed `c`: the affine core of an address/term. -/
partial def affineCore (e : Expr) : Expr :=
  match e.getAppFnArgs with
  | (``BitVec.toNat, #[_, x]) => affineCore x
  | (``HAdd.hAdd, #[_, _, _, _, x, c]) =>
      if closedTerm c then affineCore x else if closedTerm x then affineCore c else e
  | (``HSub.hSub, #[_, _, _, _, x, c]) => if closedTerm c then affineCore x else e
  | _ => e

/-- `e` is `RSP ± closed` (or an RSP alias ± closed). -/
def rspAffine (target : Nat) (taint : Array FVarId) (e : Expr) : MetaM Bool := do
  let c := affineCore e
  if let .fvar f := c then return taint.contains f
  if let some (_, i) ← regIdx? c then return i == target
  return false

/-- `e` is `v ± closed` for a variable `v` other than the state; returns `v`. -/
def varAffine (sId : FVarId) (e : Expr) : Option FVarId :=
  match affineCore e with
  | .fvar f => if f == sId then none else some f
  | _ => none

/-- Memory accesses inside `e`: (function, address-like args). An access = application of a constant with an explicit
argument of type Memory (`m.readLE a n`, `Memory.bytes m a`, any other function of a Memory). -/
partial def memAccesses (e : Expr) : MetaM (Array (Name × Array Expr)) := do
  let r ← IO.mkRef (#[] : Array (Name × Array Expr))
  let _ ← Meta.transform e (post := fun t => do
    if let .const n _ := t.getAppFn then
      let args := t.getAppArgs
      if args.size ≥ 2 then
        let mut hasMem := false
        let mut others := #[]
        for a in args do
          let ta ← (try inferType a catch _ => pure (mkConst `none))
          let ta ← instantiateMVars ta
          if isMemTy ta then hasMem := true
          else if ta.isConstOf ``Nat || ta.isAppOf ``BitVec then others := others.push a
        if hasMem && !(n == ``Eq) && !(n == ``Ne) then r.modify (·.push (n, others))
    return .continue)
  r.get

partial def subApps (e : Expr) (f : Expr → MetaM Unit) : MetaM Unit := do
  let _ ← Meta.transform e (pre := fun t => do f t; return .continue)

/-- Equation / order atoms: (lhs, rhs, kind) for every `Eq`, `LE.le`, `LT.lt` subterm. -/
def relAtoms (e : Expr) : MetaM (Array (Expr × Expr × String × Expr)) := do
  let r ← IO.mkRef #[]
  subApps e fun t => do
    match t.getAppFnArgs with
    | (``Eq, #[ty, a, b]) => r.modify (·.push (a, b, "eq", ty))
    | (``LE.le, #[ty, _, a, b]) => r.modify (·.push (a, b, "le", ty))
    | (``LT.lt, #[ty, _, a, b]) => r.modify (·.push (a, b, "le", ty))
    | (``GE.ge, #[ty, _, a, b]) => r.modify (·.push (b, a, "le", ty))
    | (``GT.gt, #[ty, _, a, b]) => r.modify (·.push (b, a, "le", ty))
    | _ => pure ()
  r.get

def fvarsOf (e : Expr) : Array FVarId := (Lean.collectFVars {} e).fvarIds

def trunc (s : String) (n : Nat := 400) : String := if s.length ≤ n then s else (s.take n).toString ++ " …"

def ppS (e : Expr) : MetaM String := do
  let f ← withOptions (fun o => o.setBool `pp.proofs false) (ppExpr e)
  return trunc ((toString f).replace "\n" " ")

/-- Analyse one precondition `pre` (a `State → Prop`), with `isa` = "amd64" | "arm64". Returns (#flags, report lines). -/
def analysePre (isa : String) (sTy pre : Expr) : MetaM (Nat × Array String) := do
  let target := if isa == "amd64" then 4 else 30
  withLocalDeclD `s sTy fun s => do
  collect (mkApp pre s) "" fun items => do
    let items ← items.mapM fun it => do return { it with e := ← instantiateMVars (← deepUnfold it.e) }
    let sId := s.fvarId!
    -- taint fixpoint (amd64 only: arm64's return address is a register, aliases cannot read it)
    let mut taint : Array FVarId := #[]
    let mut lo : Array FVarId := #[]   -- v ≤ RSP-ish
    let mut hi : Array FVarId := #[]   -- RSP-ish ≤ v
    let mut rspPinned := false
    let mut pinWhy := ""
    let mut rspLoClosed := false
    let mut rspHiClosed := false
    let mut rels := #[]
    for it in items do rels := rels ++ (← relAtoms it.e)
    for _round in [0:6] do
      for (a, b, kind, _) in rels do
        let aR ← rspAffine target taint a
        let bR ← rspAffine target taint b
        if kind == "eq" then
          if aR then if let some v := varAffine sId b then if !taint.contains v then taint := taint.push v
          if bR then if let some v := varAffine sId a then if !taint.contains v then taint := taint.push v
        else
          if bR then if let some v := varAffine sId a then lo := lo.push v
          if aR then if let some v := varAffine sId b then hi := hi.push v
      for v in lo do if hi.contains v && !taint.contains v then taint := taint.push v
    if isa == "amd64" then
      for (a, b, kind, _) in rels do
        let aR ← rspAffine target taint a
        let bR ← rspAffine target taint b
        let aC := closedTerm a
        let bC := closedTerm b
        if kind == "eq" && ((aR && bC) || (bR && aC)) then
          rspPinned := true; pinWhy := pinWhy ++ s!" [{← ppS (← mkEq a b)}]"
        if kind == "le" && aR && bC then rspHiClosed := true
        if kind == "le" && bR && aC then rspLoClosed := true
      if rspLoClosed && rspHiClosed then
        rspPinned := true; pinWhy := pinWhy ++ " [closed bounds on both sides]"
    let mut flags := 0
    let mut out := #[]
    let mut fw : Array Name := #[]
    let mut i := 0
    for it in items do
      i := i + 1
      let e := it.e
      let mut tags : Array String := #[]
      let mut info : Array String := #[]
      let mR ← mentionsReg target e
      if isa == "arm64" && mR then tags := tags.push "X30"
      -- memory accesses
      if isa == "amd64" then
        for (fn, addrs) in ← memAccesses e do
          let fnS := fn.getString!
          if fnS == "bytes" then info := info.push "BYTES"
          for a in addrs do
            if ← isAliasy target taint a then
              if let some k ← stackArg? target a then info := info.push s!"STACK-ARG(+{k})"
              else if fnS == "accessible" then info := info.push "RSP-ACCESSIBLE"
              else tags := tags.push s!"RA-READ({fnS})"
            else if rspPinned && closedTerm a then tags := tags.push s!"CONST-READ({fnS})"
      else
        for (fn, _) in ← memAccesses e do
          if fn.getString! == "bytes" then info := info.push "BYTES"
      -- whole-memory / state equations
      for (l, r, kind, ty) in ← relAtoms e do
        if kind == "eq" then
          let ty ← whnfR ty
          if isStateTy ty then tags := tags.push "MEM-EQ"
          else if ty.isForall then
            if l.containsFVar sId || r.containsFVar sId then tags := tags.push "MEM-EQ"
            else info := info.push "BINDER-EQ"
      -- opaque project constants applied to state terms
      let env ← getEnv
      let mut opq := #[]
      let r ← IO.mkRef (#[] : Array Name)
      subApps e fun t => do
        if let .const n _ := t.getAppFn then
          if ownPkg env n && t.containsFVar sId then
            match env.find? n with
            | some (.defnInfo _) | some (.ctorInfo _) | some (.recInfo _) => pure ()
            | _ => r.modify (·.push n)
      opq := (← r.get).toList.eraseDups.toArray
      for n in opq do tags := tags.push s!"OPAQUE({n})"
      if mR && tags.isEmpty && info.isEmpty then info := info.push "RSP-REL"
      if isa == "amd64" && tags.isEmpty && info.isEmpty && mentionsAny taint e then info := info.push "ALIAS-REL"
      -- framework heads
      if e.containsFVar sId then
        if let .const n _ := e.getAppFn then
          if !ownPkg env n && !fw.contains n then fw := fw.push n
      let tg := tags.toList.eraseDups
      if !tg.isEmpty then
        flags := flags + 1
        out := out.push s!"  FLAG #{i} {it.ctx}{String.intercalate "," tg}: {← ppS e}"
      else if !info.isEmpty then
        out := out.push s!"  INFO #{i} {it.ctx}{String.intercalate "," info.toList.eraseDups}: {← ppS e}"
    if rspPinned then
      flags := flags + 1
      out := out.push s!"  FLAG RSP-PIN:{pinWhy}"
    if !taint.isEmpty then
      let names ← taint.mapM fun f => do return toString (← f.getUserName)
      out := out.push s!"  INFO RSP aliases: {names.toList}"
    out := out.push s!"  INFO FRAMEWORK heads applied to s: {fw.toList}"
    return (flags, #[s!"  conjuncts: {items.size}"] ++ out)

/-- Every Janus main-theorem form inside a statement: (constant, pre). -/
def findPres (body : Expr) : MetaM (Array (Name × Expr)) := do
    let r ← IO.mkRef #[]
    let env ← getEnv
    subApps body fun t => do
      if let .const n _ := t.getAppFn then
        if (`Janus).isPrefixOf n then
          if let some ci := env.find? n then
            let mut i := 0
            let mut ty := ci.type
            let args := t.getAppArgs
            let mut idx? : Option Nat := none
            while ty.isForall do
              if ty.bindingName! == `pre then idx? := some i
              ty := ty.bindingBody!; i := i + 1
            if let some idx := idx? then
              if let some p := args[idx]? then r.modify (·.push (n, p))
    r.get

elab "#ra_pin_audit " id:ident isa:str : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let ci ← getConstInfo n
  let isa := isa.getString
  forallTelescope ci.type fun _ body => do
  let pres ← findPres body
  if pres.isEmpty then
    IO.println s!"RAPIN {isa} {n}: NO-FORM (no Janus constant with a `pre` binder in the statement)"; return
  let mut total := 0
  let mut lines := #[]
  for (form, pre) in pres do
    let pty ← whnf (← inferType pre)
    let (k, ls) ← match pty with
      | .forallE _ sTy _ _ => analysePre isa sTy pre
      | _ => pure (1, #[s!"  FLAG pre has unexpected type {← ppS pty}"])
    total := total + k
    lines := lines.push (s!" form {form}:" :: ls.toList)
  let verdict := if total == 0 then "CLEAN" else s!"{total} FLAG(S)"
  IO.println s!"RAPIN {isa} {n}: {verdict}"
  for l in lines do for x in l do IO.println x

end RaPin

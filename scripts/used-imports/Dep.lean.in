import FvModexp.Proofs.Arm64.Exp.W4FunE
open Lean

def pfx : String := "FvModexp.Proofs.Arm64.Exp."

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (c : Name) : Option Name := (env.getModuleIdxFor? c).map (fun i => mods[i.toNat]!)
  let mut used : Std.HashMap Name (Std.HashSet Name) := {}
  for (c, ci) in env.constants.toList do
    let some m := modOf c | continue
    unless m.toString.startsWith pfx do continue
    let mut s := used.getD m {}
    let cs := ci.type.getUsedConstants ++ (match ci with | .thmInfo v => v.value.getUsedConstants | _ => (ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    for d in cs do
      if let some m2 := modOf d then
        if m2 != m then s := s.insert m2
    used := used.insert m s
  for (m, s) in used.toList do
    let l := s.toList.filter (fun x => x.toString.startsWith "FvModexp.") |>.map toString |>.toArray.qsort (· < ·)
    IO.println s!"{m}: {l}"

# divmc s38: mechanical arm64 -> amd64 transform of Arm64/NatQ/KSqr* (hand fixes follow). usage: port64.py MOD...
import re, sys
for m in sys.argv[1:]:
    s = open('FvModexp/Proofs/Arm64/NatQ/%s.lean' % m).read()
    s = re.sub(r'^import FvModexp\.Proofs\.Arm64\.', 'import FvModexp.Proofs.Amd64.', s, flags=re.M)
    s = s.replace('open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts',
                  'open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts')
    s = s.replace('FvModexp.Arm64.', 'FvModexp.Amd64.')
    s = re.sub(r"\b([A-Za-z_][A-Za-z0-9_']*)\.sp\.toNat", r'(\1.regs 4).toNat', s)
    s = re.sub(r'\bregs 28\b', 'regs 14', s)
    s = re.sub(r'\bwinA\b', 'win', s)
    s = re.sub(r'(?<![\w.])Memory\.accessible_(mono|sub)', r'Janus.Arm64.Memory.accessible_\1', s)
    s = s.replace('(impl : List Segment)', '(impl : List Amd64.Segment)').replace('{impl : List Segment}', '{impl : List Amd64.Segment}')
    s = s.replace('(hap : ImplApart Extracted.program impl)', '(hap : Amd64.ImplApart Extracted.program impl)')
    for c in ['MakesliceLiveContract','GrowsliceLiveContract','MemclrNoHeapPointersLive','WbLiveContract','MemmoveLive','NewobjectLiveContract']:
        s = re.sub(r'\b%s\b(?!64)' % c, c + '64', s)
    s = s.replace('# [Q-form copy of Arm64/Nat/', '# [amd64 port (divmc s38) of the Q-form Arm64/NatQ/').replace('— TIGHT COSTS, divmc s34]', '— TIGHT COSTS]')
    open('FvModexp/Proofs/Amd64/NatQ/%s.lean' % m, 'w').write(s)
    print(m, len(re.findall(r'regs 30|regs 29|\.pc\b|0x1b[0-9a-f]{4}', s)), 'arm64-specific sites left')

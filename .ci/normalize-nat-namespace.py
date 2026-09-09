from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

# The canonical monolith repair may already have removed the unqualified Nat
# import. This pass is intentionally idempotent and accepts either state.
imports = [
    'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)',
    'open import Agda.Builtin.Nat using (Nat; suc; _+_)',
    'open import Agda.Builtin.Nat using (Nat; suc)',
]
if imports[0] in text:
    text = text.replace(imports[0], imports[2], 1)
elif imports[1] in text:
    text = text.replace(imports[1], imports[2], 1)
elif imports[2] not in text:
    raise SystemExit('no supported Nat import form found')

patterns = [
    ('  [] : Vec A zero\n', '  [] : Vec A Nat.zero\n'),
    ('[] : Vec A zero', '[] : Vec A Nat.zero'),
    ('sumFin _ z zero _ = z\n', 'sumFin _ z Nat.zero _ = z\n'),
    ('sumFin _ z zero _ =', 'sumFin _ z Nat.zero _ ='),
    ('tabulateV {zero} f =', 'tabulateV {Nat.zero} f ='),
    ('zeroVector {S} {zero} =', 'zeroVector {S} {Nat.zero} ='),
    ('zeroVecS {S} {zero} =', 'zeroVecS {S} {Nat.zero} ='),
    ('tabulateVS {S} {zero} f =', 'tabulateVS {S} {Nat.zero} f ='),
    ('maskAllFalse {zero} =', 'maskAllFalse {Nat.zero} ='),
    ('allActive_v147 {zero} =', 'allActive_v147 {Nat.zero} ='),
    ('qRunFuel_v142 zero r =', 'qRunFuel_v142 Nat.zero r ='),
    ('natSub_v146 zero _ =', 'natSub_v146 Nat.zero _ ='),
    ('natPlusSucc_v141 zero n =', 'natPlusSucc_v141 Nat.zero n ='),
]
for old, new in patterns:
    text = text.replace(old, new)

text = text.replace('{zero} = []', '{Nat.zero} = []')
text = text.replace('{zero} f = []', '{Nat.zero} f = []')
text = text.replace('{S} {zero} = []', '{S} {Nat.zero} = []')
text = text.replace('{S} {zero} f = []', '{S} {Nat.zero} f = []')

# Once the Nat constructor import is qualified, find remaining bare Nat-zero
# constructor uses without touching algebraic Ring.zero occurrences.
lines = []
for line in text.splitlines(keepends=True):
    if 'Nat.zero' not in line and 'zero' in line:
        stripped = line.lstrip()
        if stripped.startswith(('data ', 'sumFin ', 'qRunFuel_', 'natSub_', 'natPlusSucc_')):
            line = line.replace(' zero ', ' Nat.zero ')
        elif ' {zero}' in line or '{zero} ' in line:
            line = line.replace('{zero}', '{Nat.zero}')
        elif ' Vec ' in line and ' zero' in line:
            line = line.replace(' Vec A zero', ' Vec A Nat.zero')
    lines.append(line)
text = ''.join(lines)

if 'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)' in text:
    raise SystemExit('unqualified Nat zero import survived')
if 'open import Agda.Builtin.Nat using (Nat; suc; _+_)' in text:
    raise SystemExit('unqualified Nat addition import survived')
if '  [] : Vec A zero\n' in text or '[] : Vec A zero' in text:
    raise SystemExit('unqualified Nat.zero Vec base constructor survived')

path.write_text(text)
print('nat-namespace-normalized=True')

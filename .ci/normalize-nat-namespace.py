from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

old = 'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)'
new = 'open import Agda.Builtin.Nat using (Nat; suc)'
if old in text:
    text = text.replace(old, new, 1)
elif 'open import Agda.Builtin.Nat using (Nat; suc)' not in text:
    raise SystemExit('Nat import shape not found')

patterns = [
    ('  [] : Vec A zero\n', '  [] : Vec A Nat.zero\n'),
    ('sumFin _ z zero _ = z\n', 'sumFin _ z Nat.zero _ = z\n'),
    ('tabulateV {zero} f =', 'tabulateV {Nat.zero} f ='),
    ('zeroVector {S} {zero} =', 'zeroVector {S} {Nat.zero} ='),
    ('zeroVecS {S} {zero} =', 'zeroVecS {S} {Nat.zero} ='),
    ('tabulateVS {S} {zero} f =', 'tabulateVS {S} {Nat.zero} f ='),
    ('maskAllFalse {zero} =', 'maskAllFalse {Nat.zero} ='),
    ('allActive_v147 {zero} =', 'allActive_v147 {Nat.zero} ='),
    ('qRunFuel_v142 zero r =', 'qRunFuel_v142 Nat.zero r ='),
    ('natSub_v146 zero _ =', 'natSub_v146 Nat.zero _ ='),
    ('natPlusSucc_v141 zero n =', 'natPlusSucc_v141 Nat.zero n ='),
    ('qRunFuel_v142 zero r = r', 'qRunFuel_v142 Nat.zero r = r'),
    ('natSub_v146 zero _ = zero', 'natSub_v146 Nat.zero _ = zero'),
    ('natPlusSucc_v141 zero n = refl', 'natPlusSucc_v141 Nat.zero n = refl'),
]
for old, new in patterns:
    text = text.replace(old, new)

text = text.replace('{zero} = []', '{Nat.zero} = []')
text = text.replace('{zero} f = []', '{Nat.zero} f = []')
text = text.replace('{S} {zero} = []', '{S} {Nat.zero} = []')
text = text.replace('{S} {zero} f = []', '{S} {Nat.zero} f = []')

if 'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)' in text:
    raise SystemExit('unqualified Nat zero import survived')
if '  [] : Vec A zero\n' in text:
    raise SystemExit('unqualified Nat.zero Vec base constructor survived')

path.write_text(text)
print('nat-namespace-normalized=True')

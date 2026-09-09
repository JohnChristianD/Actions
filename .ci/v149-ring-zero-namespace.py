from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

# Nat.zero and Nat._+_ both collide with the scalar Ring field names when
# imported unqualified. Keep Nat._+_ out of the open namespace as well.
s = s.replace(
    'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)',
    'open import Agda.Builtin.Nat using (Nat; suc)',
    1,
)
s = s.replace(
    'open import Agda.Builtin.Nat using (Nat; suc; _+_)',
    'open import Agda.Builtin.Nat using (Nat; suc)',
    1,
)

patterns = [
    ('[] : Vec A zero', '[] : Vec A Nat.zero'),
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
    s = s.replace(old, new)

s = s.replace('{zero} = []', '{Nat.zero} = []')
s = s.replace('{zero} f = []', '{Nat.zero} f = []')
s = s.replace('{S} {zero} = []', '{S} {Nat.zero} = []')
s = s.replace('{S} {zero} f = []', '{S} {Nat.zero} f = []')

if 'open import Agda.Builtin.Nat using (Nat; zero' in s:
    raise SystemExit('unqualified Nat.zero import survived')
if 'open import Agda.Builtin.Nat using (Nat; suc; _+_)' in s:
    raise SystemExit('unqualified Nat._+_ import survived')
if '[] : Vec A zero' in s:
    raise SystemExit('unqualified Nat.zero Vec constructor survived')

p.write_text(s)
print('Nat namespace normalization applied deterministically')

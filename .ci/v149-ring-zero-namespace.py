from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

# `Nat.zero` and the scalar Ring field `zero` must not share an unqualified
# namespace in Agda 2.8.0.  Keep scalar algebraic `zero` untouched and qualify
# only constructor/index occurrences.
s = s.replace(
    'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)',
    'open import Agda.Builtin.Nat using (Nat; suc; _+_)',
    1,
)

nat_zero_patterns = [
    ('[] : Vec A zero', '[] : Vec A Nat.zero'),
    ('sumFin _ z zero _ =', 'sumFin _ z Nat.zero _ ='),
    ('tabulateV {zero} f =', 'tabulateV {Nat.zero} f ='),
    ('zeroVecS {S} {zero} =', 'zeroVecS {S} {Nat.zero} ='),
    ('tabulateVS {S} {zero} f =', 'tabulateVS {S} {Nat.zero} f ='),
    ('maskAllFalse {zero} =', 'maskAllFalse {Nat.zero} ='),
    ('qRunFuel_v142 zero r =', 'qRunFuel_v142 Nat.zero r ='),
    ('natSub_v146 zero _ =', 'natSub_v146 Nat.zero _ ='),
    ('natPlusSucc_v141 zero n =', 'natPlusSucc_v141 Nat.zero n ='),
    ('l2Effective_v146 h with CoupledHyperParameters_v146.l2ZeroDecision h',
     'l2Effective_v146 h with CoupledHyperParameters_v146.l2ZeroDecision h'),
    ('replayPrefix_v141 st [] = st', 'replayPrefix_v141 st [] = st'),
]
for old, new in nat_zero_patterns:
    s = s.replace(old, new)

# Parameterized Nat-index patterns occurring in finite vector recursors.
s = s.replace('{zero} = []', '{Nat.zero} = []')
s = s.replace('{zero} f = []', '{Nat.zero} f = []')
s = s.replace('{S} {zero} = []', '{S} {Nat.zero} = []')
s = s.replace('{S} {zero} f = []', '{S} {Nat.zero} f = []')

# Remaining exact Nat recursion heads used by the monolith.
s = s.replace('vZero_v140 {S} {zero} = []', 'vZero_v140 {S} {Nat.zero} = []')
s = s.replace('allActive_v147 {zero} = []', 'allActive_v147 {Nat.zero} = []')
s = s.replace('maskAllFalse {zero} = []', 'maskAllFalse {Nat.zero} = []')
s = s.replace('natSub_v146 zero _ = zero', 'natSub_v146 Nat.zero _ = zero')
s = s.replace('qRunFuel_v142 zero r = r', 'qRunFuel_v142 Nat.zero r = r')
s = s.replace('natPlusSucc_v141 zero n = refl', 'natPlusSucc_v141 Nat.zero n = refl')

# The finite Vec definition is the first scope point at which the clash
# manifests, so assert that it is corrected rather than silently relying on
# later normalization.
if '[] : Vec A zero' in s:
    raise SystemExit('unqualified Nat.zero remains in Vec base constructor')
if '[] : Vec A Nat.zero' not in s:
    raise SystemExit('qualified Nat.zero Vec constructor missing')
if 'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)' in s:
    raise SystemExit('unqualified Nat zero import survived')

p.write_text(s)
print('Nat.zero namespace normalization applied deterministically')
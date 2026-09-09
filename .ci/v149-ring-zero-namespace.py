from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

# Keep scalar `zero` available while removing the global Nat constructor
# `zero`, whose name clashes with the Ring record field `zero`.
s = s.replace(
    'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)',
    'open import Agda.Builtin.Nat using (Nat; suc; _+_)',
    1,
)

# Nat zero occurs only as a constructor in Nat-indexed pattern positions or
# explicit Nat values.  Rewrite those syntactic positions, leaving scalar
# algebraic `zero` untouched.
s = re.sub(r'(?m)(\{(?:[^\n{}]*\b)?)(zero)(\})', r'\1Nat.zero\3', s)
s = re.sub(r'(?m)(\b(?:=|→|,)\s*)(zero)(\b)', lambda m: m.group(1) + ('Nat.zero' if '→' in m.group(1) or '=' in m.group(1) else 'zero') + m.group(3), s)

# Constructor patterns at the head of a clause with expected Nat input.
# These are confined to known Nat recurrences and definitions.
for old, new in [
    ('sumFin _ z zero _ =', 'sumFin _ z Nat.zero _ ='),
    ('tabulateV {zero} f =', 'tabulateV {Nat.zero} f ='),
    ('zeroVecS {S} {zero} =', 'zeroVecS {S} {Nat.zero} ='),
    ('tabulateVS {S} {zero} f =', 'tabulateVS {S} {Nat.zero} f ='),
    ('qMuZeroFromNumLe_v147 D budget mask alpha x h with', 'qMuZeroFromNumLe_v147 D budget mask alpha x h with'),
    ('allActive_v147 : ∀ {n} → Vec Bool n\nallActive_v147 {zero} = []', 'allActive_v147 : ∀ {n} → Vec Bool n\nallActive_v147 {Nat.zero} = []'),
    ('maskAllFalse : ∀ {n} → Vec Bool n\nmaskAllFalse {zero} = []', 'maskAllFalse : ∀ {n} → Vec Bool n\nmaskAllFalse {Nat.zero} = []'),
    ('qRunFuel_v142 zero r = r', 'qRunFuel_v142 Nat.zero r = r'),
    ('replayAge_v146 sampleTime currentTime = natSub_v146 currentTime sampleTime', 'replayAge_v146 sampleTime currentTime = natSub_v146 currentTime sampleTime'),
    ('natSub_v146 zero _ = zero', 'natSub_v146 Nat.zero _ = zero'),
    ('qFirstNegative_v142 {S} D [] [] [] mu = nothing', 'qFirstNegative_v142 {S} D [] [] [] mu = nothing'),
]:
    s = s.replace(old, new)

# Remaining Nat-zero clause patterns caught by these exact structural forms.
s = s.replace('qRunFuel_v142 zero r = r', 'qRunFuel_v142 Nat.zero r = r')
s = s.replace('natSub_v146 zero _ = zero', 'natSub_v146 Nat.zero _ = zero')
s = s.replace('natPlusSucc_v141 zero n = refl', 'natPlusSucc_v141 Nat.zero n = refl')

p.write_text(s)
print('Nat.zero namespace normalization applied')
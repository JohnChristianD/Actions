from pathlib import Path
import re

# Canonical safe-closure namespace normalizer: deterministic structural compatibility only.
p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
replacements = {
    'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)': 'open import Agda.Builtin.Nat using (Nat; suc)',
    'open import Agda.Builtin.Nat using (Nat; suc; _+_)': 'open import Agda.Builtin.Nat using (Nat; suc)',
    'open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong; subst)': 'open import Agda.Builtin.Equality using (_≡_; refl)',
}
for old, new in replacements.items():
    s = s.replace(old, new)

if 'cong : ∀ {A B : Set}' not in s:
    marker = 'cong₂ f refl refl = refl\n'
    helper = marker + '''
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px
'''
    if marker not in s:
        raise SystemExit('expected cong₂ helper marker not found')
    s = s.replace(marker, helper, 1)

for old, new in {
    '  [] : Vec A zero': '  [] : Vec A Nat.zero',
    'sumFin _ z zero _ = z': 'sumFin _ z Nat.zero _ = z',
    'qRunFuel_v142 zero r = r': 'qRunFuel_v142 Nat.zero r = r',
    'natPlusSucc_v141 zero n = refl': 'natPlusSucc_v141 Nat.zero n = refl',
    'takeV_v146 zero _ = []': 'takeV_v146 Nat.zero _ = []',
    'shiftLV_v146 zero xs = xs': 'shiftLV_v146 Nat.zero xs = xs',
    'shiftRV_v146 zero xs = xs': 'shiftRV_v146 Nat.zero xs = xs',
    'qsaXorShiftDeterministic_v146 zero seed = []': 'qsaXorShiftDeterministic_v146 Nat.zero seed = []',
    'oracleCrossCheckSurface_v146 = suc (suc (suc zero))': 'oracleCrossCheckSurface_v146 = suc (suc (suc Nat.zero))',
    '  natLeZero : ∀ {n} → NatLe zero n': '  natLeZero : ∀ {n} → NatLe Nat.zero n',
    'natSub_v146 zero _ = zero': 'natSub_v146 Nat.zero _ = Nat.zero',
    'natSub_v146 (suc m) zero = suc m': 'natSub_v146 (suc m) Nat.zero = suc m',
    'natSubAddLeft_v146 zero b = refl': 'natSubAddLeft_v146 Nat.zero b = refl',
    'qRunProjectionFormFuel_v147 zero r = refl': 'qRunProjectionFormFuel_v147 Nat.zero r = refl',
    '... | nothing = qRunProjectionFormFuel_v147 zero r': '... | nothing = qRunProjectionFormFuel_v147 Nat.zero r',
    'qRunStopsWhenNoNegative_v147 zero r h = refl': 'qRunStopsWhenNoNegative_v147 Nat.zero r h = refl',
    'Vec A (m + n)': 'Vec A (Nat._+_ m n)',
    '∀ a n → a + suc n ≡ suc (a + n)': '∀ a n → Nat._+_ a (suc n) ≡ suc (Nat._+_ a n)',
    'ReplayState_v141.time st + n': 'Nat._+_ (ReplayState_v141.time st) n',
    'natSub_v146 (a + b) a': 'natSub_v146 (Nat._+_ a b) a',
    'sampleTime + (delay₁ + delay₂)': 'Nat._+_ sampleTime (Nat._+_ delay₁ delay₂)',
    'sampleTime + delay': 'Nat._+_ sampleTime delay',
    'delay₁ + delay₂': 'Nat._+_ delay₁ delay₂',
}.items():
    s = s.replace(old, new)

start = s.index('record OrderedRing')
end = s.index('record SmoothAlgebra', start)
block = s[start:end]
block = block.replace('a * b', 'Ring._*_ ring a b')
block = block.replace('c * a', 'Ring._*_ ring c a')
block = block.replace('c * b', 'Ring._*_ ring c b')
block = block.replace('a + c', 'Ring._+_ ring a c')
block = block.replace('b + d', 'Ring._+_ ring b d')
block = block.replace('c + a', 'Ring._+_ ring c a')
block = block.replace('c + b', 'Ring._+_ ring c b')
block = block.replace('a + neg b', 'Ring._+_ ring a (Ring.neg ring b)')
block = block.replace('x * x', 'Ring._*_ ring x x')
block = block.replace('x ≠ zero', '¬ (x ≡ zero)')
block = block.replace(
    'abs (x + y) ≤ abs x + abs y',
    'abs (Ring._+_ ring x y) ≤ Ring._+_ ring (abs x) (abs y)',
)
s = s[:start] + block + s[end:]

old_minus = '  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)\n  minus x y = Ring._+_ Rg x (Ring.neg Rg y)'
new_minus = '  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)\n  minus : Scalar S → Scalar S → Scalar S\n  minus x y = Ring._+_ Rg x (Ring.neg Rg y)'
s = s.replace(old_minus, new_minus)

# Keep record field `hidden` distinct from its Nat dimension parameter.
s = s.replace(
    'record RecurrentAffine (S : SmoothAlgebra) (input hidden : Nat) : Set where',
    'record RecurrentAffine (S : SmoothAlgebra) (input hiddenDim : Nat) : Set where',
)
s = s.replace('MatS S hidden input', 'MatS S hiddenDim input')
s = s.replace('MatS S hidden hidden', 'MatS S hiddenDim hiddenDim')
s = s.replace('VecS S hidden\n    norm : LayerNorm S hidden', 'VecS S hiddenDim\n    norm : LayerNorm S hiddenDim')
s = s.replace(
    'record LSTMGates (S : SmoothAlgebra) (input hidden : Nat) : Set where',
    'record LSTMGates (S : SmoothAlgebra) (input hiddenDim : Nat) : Set where',
)
s = s.replace('RecurrentAffine S input hidden', 'RecurrentAffine S input hiddenDim')
s = s.replace(
    'record LSTMBlock (S : SmoothAlgebra) (input hidden : Nat) : Set where',
    'record LSTMBlock (S : SmoothAlgebra) (input hiddenDim : Nat) : Set where',
)
s = s.replace('LSTMGates S input hidden', 'LSTMGates S input hiddenDim')
s = s.replace(
    'record LSTMState (S : SmoothAlgebra) (hidden : Nat) : Set where',
    'record LSTMState (S : SmoothAlgebra) (hiddenDim : Nat) : Set where',
)
s = s.replace('VecS S hidden\n', 'VecS S hiddenDim\n')

start = s.index('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = s.index('\n------------------------------------------------------------------------\n-- Neural components:', start)
segment = s[start:end]
segment = re.sub(r'\bR\b', 'ScalarR', segment)
segment = segment.replace('Ring.ScalarR', 'Ring.R')
segment = segment.replace('eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i', 'Ring._+_ R (Ring._*_ R (eval y ρ) (coeff x ρ i)) (Ring._*_ R (eval x ρ) (coeff y ρ i))')
for name in ('dexp', 'dlog', 'dtanh', 'dsigmoid'):
    segment = segment.replace(f'{name} (eval x ρ) * coeff x ρ i', f'Ring._*_ R ({name} (eval x ρ)) (coeff x ρ i)')
s = s[:start] + segment + s[end:]

p.write_text(s)
print('completesafe-namespace-normalization=qualified-orderedring-block-equality-basis-minus-recurrent-hiddenDim')
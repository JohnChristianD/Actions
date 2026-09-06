from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
replacements = {
    'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)': 'open import Agda.Builtin.Nat using (Nat; suc)',
    'open import Agda.Builtin.Nat using (Nat; suc; _+_)': 'open import Agda.Builtin.Nat using (Nat; suc)',
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
    '    addLe : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d': '    addLe : ∀ {a b c d} → a ≤ b → c ≤ d → Ring._+_ ring a c ≤ Ring._+_ ring b d',
    '    mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ a * b': '    mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ Ring._*_ ring a b',
    '    mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → c * a ≤ c * b': '    mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → Ring._*_ ring c a ≤ Ring._*_ ring c b',
    '    ltAdd : ∀ {a b c d} → a < b → c < d → a + c < b + d': '    ltAdd : ∀ {a b c d} → a < b → c < d → Ring._+_ ring a c < Ring._+_ ring b d',
    '    addLtLeft : ∀ {a b c} → a < b → c + a < c + b': '    addLtLeft : ∀ {a b c} → a < b → Ring._+_ ring c a < Ring._+_ ring c b',
    '    mulLtPosLeft : ∀ {a b c} → a < b → zero < c → c * a < c * b': '    mulLtPosLeft : ∀ {a b c} → a < b → zero < c → Ring._*_ ring c a < Ring._*_ ring c b',
    '    mulLtPosCancelLeft : ∀ {a b c} → c * a < c * b → zero < c → a < b': '    mulLtPosCancelLeft : ∀ {a b c} → Ring._*_ ring c a < Ring._*_ ring c b → zero < c → a < b',
    '    mulPos : ∀ {a b} → zero < a → zero < b → zero < a * b': '    mulPos : ∀ {a b} → zero < a → zero < b → zero < Ring._*_ ring a b',
    '    subLtZero : ∀ {a b} → a + neg b < zero → a < b': '    subLtZero : ∀ {a b} → Ring._+_ ring a (neg b) < zero → a < b',
    '    squarePositive : ∀ {x} → x ≠ zero → zero < x * x': '    squarePositive : ∀ {x} → x ≠ zero → zero < Ring._*_ ring x x',
    '    squareNonnegative : ∀ x → zero ≤ x * x': '    squareNonnegative : ∀ x → zero ≤ Ring._*_ ring x x',
    '    absTriangle : ∀ x y → abs (x + y) ≤ abs x + abs y': '    absTriangle : ∀ x y → abs (Ring._+_ ring x y) ≤ Ring._+_ ring (abs x) (abs y)',
    '    absMul : ∀ x y → abs (x * y) ≡ abs x * abs y': '    absMul : ∀ x y → abs (Ring._*_ ring x y) ≡ Ring._*_ ring (abs x) (abs y)',
    '    fromNatSuc : ∀ n → fromNat (suc n) ≡ fromNat n + one': '    fromNatSuc : ∀ n → fromNat (suc n) ≡ Ring._+_ ring (fromNat n) one',
}
for old, new in replacements.items():
    s = s.replace(old, new)
p.write_text(s)
print('completesafe-namespace-normalization=qualified-Nat-arithmetic-and-OrderedRing-operators')

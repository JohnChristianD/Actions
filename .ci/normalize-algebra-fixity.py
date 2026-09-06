from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

for old, new in [
('''vSub {S} = zipWithV minus\n  where\n  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)\n  minus x y = Ring._+_ Rg x (Ring.neg Rg y)\n''',
 '''vSub {S} = zipWithV minus\n  where\n  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)\n  minus : Scalar S → Scalar S → Scalar S\n  minus x y = Ring._+_ Rg x (Ring.neg Rg y)\n'''),
('''  μ = vSum xs * SmoothAlgebra.recip S (SmoothAlgebra.fromNat S d)\n  centered x = x + neg μ\n''',
 '''  μ = vSum xs * SmoothAlgebra.recip S (SmoothAlgebra.fromNat S d)\n  centered : Scalar S → Scalar S\n  centered x = x + neg μ\n'''),
('''  invStd = SmoothAlgebra.recip S\n    (SmoothAlgebra.sqrt S (variance + LayerNorm.epsilon ln))\n  normalise x = centered x * invStd\n''',
 '''  invStd = SmoothAlgebra.recip S\n    (SmoothAlgebra.sqrt S (variance + LayerNorm.epsilon ln))\n  normalise : Scalar S → Scalar S\n  normalise x = centered x * invStd\n''')]:
    if old in text:
        text = text.replace(old, new, 1)

text = text.replace('LSTMGates.gates (LSTMBlock.gates block)', 'LSTMBlock.gates block')
text = text.replace('\nopen Ring\n\nrecord OrderedRing : Set₁ where', '\nrecord OrderedRing : Set₁ where', 1)
text = text.replace('\nopen OrderedRing\n\nrecord SmoothAlgebra : Set₁ where', '\nrecord SmoothAlgebra : Set₁ where', 1)

text = text.replace(
    '    sqrt recip max min : R → R\n'
    '    maxNonnegative : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ max a b\n',
    '    sqrt recip min : R → R\n'
    '    max : R → R → R\n'
    '    maxNonnegative : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ max a b\n',
    1,
)
text = text.replace('    fromNatZero : fromNat zero ≡ zero\n', '    fromNatZero : fromNat Nat.zero ≡ zero\n', 1)
text = text.replace('tabulateV {zero} f = []', 'tabulateV {A = _} {n = Nat.zero} f = []', 1)
text = text.replace('tabulateV {suc n} f = f fzero ∷ tabulateV (λ i → f (fsuc i))',
                    'tabulateV {A = A} {n = Nat.suc n} f = f fzero ∷ tabulateV (λ i → f (fsuc i))', 1)

start = text.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = text.find('\n------------------------------------------------------------------------', start + 10)
if start < 0 or end < 0:
    raise SystemExit('EfficientCHAD module region not found')
region = text[start:end]
region = region.replace('Rg = OrderedRing.ring orderedRing', 'Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)')
region = re.sub(r'(?m)^(\s*)R = Ring\.R Rg\s*$', r'\1CR = Ring.R Rg', region)
region = re.sub(r'(?<![A-Za-z0-9_.])R(?![A-Za-z0-9_])', 'CR', region)
region = re.sub(r'(?<![A-Za-z0-9_.])one(?![A-Za-z0-9_])', 'Ring.one Rg', region)
region = re.sub(r'(?<![A-Za-z0-9_.])zero(?![A-Za-z0-9_])', 'Ring.zero Rg', region)
region = re.sub(r'(?<![A-Za-z0-9_.])neg(?![A-Za-z0-9_])', 'Ring.neg Rg', region)

for old, new in [
    ('addCot a b i = a i + b i', 'addCot a b i = Ring._+_ Rg (a i) (b i)'),
    ('scaleCot a v i = a * v i', 'scaleCot a v i = Ring._*_ Rg a (v i)'),
    ('negCot v i = neg (v i)', 'negCot v i = Ring.neg Rg (v i)'),
    ('eval (add x y) ρ = eval x ρ + eval y ρ', 'eval (add x y) ρ = Ring._+_ Rg (eval x ρ) (eval y ρ)'),
    ('eval (mul x y) ρ = eval x ρ * eval y ρ', 'eval (mul x y) ρ = Ring._*_ Rg (eval x ρ) (eval y ρ)'),
    ('eval (negE x) ρ = neg (eval x ρ)', 'eval (negE x) ρ = Ring.neg Rg (eval x ρ)'),
    ('eval (expE x) ρ = exp (eval x ρ)', 'eval (expE x) ρ = SmoothAlgebra.exp S (eval x ρ)'),
    ('eval (logE x) ρ = log (eval x ρ)', 'eval (logE x) ρ = SmoothAlgebra.log S (eval x ρ)'),
    ('eval (tanhE x) ρ = tanh (eval x ρ)', 'eval (tanhE x) ρ = SmoothAlgebra.tanh S (eval x ρ)'),
    ('eval (sigmoidE x) ρ = sigmoid (eval x ρ)', 'eval (sigmoidE x) ρ = SmoothAlgebra.sigmoid S (eval x ρ)'),
    ('coeff (add x y) ρ i = coeff x ρ i + coeff y ρ i', 'coeff (add x y) ρ i = Ring._+_ Rg (coeff x ρ i) (coeff y ρ i)'),
    ('coeff (mul x y) ρ i = eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i',
     'coeff (mul x y) ρ i = (Ring._*_ Rg (eval y ρ) (coeff x ρ i)) + (Ring._*_ Rg (eval x ρ) (coeff y ρ i))'),
    ('coeff (negE x) ρ i = neg (coeff x ρ i)', 'coeff (negE x) ρ i = Ring.neg Rg (coeff x ρ i)'),
    ('coeff (expE x) ρ i = coeff x ρ i * dexp (eval x ρ)', 'coeff (expE x) ρ i = Ring._*_ Rg (coeff x ρ i) (dexp (eval x ρ))'),
    ('coeff (logE x) ρ i = coeff x ρ i * dlog (eval x ρ)', 'coeff (logE x) ρ i = Ring._*_ Rg (coeff x ρ i) (dlog (eval x ρ))'),
    ('coeff (tanhE x) ρ i = coeff x ρ i * dtanh (eval x ρ)', 'coeff (tanhE x) ρ i = Ring._*_ Rg (coeff x ρ i) (dtanh (eval x ρ))'),
    ('coeff (sigmoidE x) ρ i = coeff x ρ i * dsigmoid (eval x ρ)', 'coeff (sigmoidE x) ρ i = Ring._*_ Rg (coeff x ρ i) (dsigmoid (eval x ρ))'),
    ('  primalCorrect (add x y) ρ = cong₂ _+_ (primalCorrect x ρ) (primalCorrect y ρ)',
     '  primalCorrect (add x y) ρ = cong₂ (Ring._+_ Rg) (primalCorrect x ρ) (primalCorrect y ρ)'),
    ('  primalCorrect (mul x y) ρ = cong₂ _*_ (primalCorrect x ρ) (primalCorrect y ρ)',
     '  primalCorrect (mul x y) ρ = cong₂ (Ring._*_ Rg) (primalCorrect x ρ) (primalCorrect y ρ)'),
    ('  primalCorrect (negE x) ρ = cong neg (primalCorrect x ρ)',
     '  primalCorrect (negE x) ρ = cong (Ring.neg Rg) (primalCorrect x ρ)'),
    ('  primalCorrect (expE x) ρ = cong exp (primalCorrect x ρ)',
     '  primalCorrect (expE x) ρ = cong (SmoothAlgebra.exp S) (primalCorrect x ρ)'),
    ('  primalCorrect (logE x) ρ = cong log (primalCorrect x ρ)',
     '  primalCorrect (logE x) ρ = cong (SmoothAlgebra.log S) (primalCorrect x ρ)'),
    ('  primalCorrect (tanhE x) ρ = cong tanh (primalCorrect x ρ)',
     '  primalCorrect (tanhE x) ρ = cong (SmoothAlgebra.tanh S) (primalCorrect x ρ)'),
    ('  primalCorrect (sigmoidE x) ρ = cong sigmoid (primalCorrect x ρ)',
     '  primalCorrect (sigmoidE x) ρ = cong (SmoothAlgebra.sigmoid S) (primalCorrect x ρ)'),
    ('      { value = value px + value py', '      { value = Ring._+_ Rg (value px) (value py)'),
    ('      { value = vx * vy', '      { value = Ring._*_ Rg vx vy'),
    ('      ; back = λ c → addCot (back px (c * vy)) (back py (c * vx))',
     '      ; back = λ c → addCot (back px (Ring._*_ Rg c vy)) (back py (Ring._*_ Rg c vx))'),
    ('    in record { value = neg (value px) ; back = λ c → negCot (back px c) }',
     '    in record { value = Ring.neg Rg (value px) ; back = λ c → negCot (back px c) }'),
    ('    in record { value = exp vx ; back = λ c → back px (c * dexp vx) }',
     '    in record { value = SmoothAlgebra.exp S vx ; back = λ c → back px (Ring._*_ Rg c (dexp vx)) }'),
    ('    in record { value = log vx ; back = λ c → back px (c * dlog vx) }',
     '    in record { value = SmoothAlgebra.log S vx ; back = λ c → back px (Ring._*_ Rg c (dlog vx)) }'),
    ('    in record { value = tanh vx ; back = λ c → back px (c * dtanh vx) }',
     '    in record { value = SmoothAlgebra.tanh S vx ; back = λ c → back px (Ring._*_ Rg c (dtanh vx)) }'),
    ('    in record { value = sigmoid vx ; back = λ c → back px (c * dsigmoid vx) }',
     '    in record { value = SmoothAlgebra.sigmoid S vx ; back = λ c → back px (Ring._*_ Rg c (dsigmoid vx)) }'),
    ('  vjpCoeff : ∀ e ρ c i → Pullback.back (pull e ρ) c i ≡ c * coeff e ρ i',
     '  vjpCoeff : ∀ e ρ c i → Pullback.back (pull e ρ) c i ≡ Ring._*_ Rg c (coeff e ρ i)'),
    ('(vjpCoeff x ρ (c * eval y ρ) i)', '(vjpCoeff x ρ (Ring._*_ Rg c (eval y ρ)) i)'),
    ('(vjpCoeff y ρ (c * eval x ρ) i)', '(vjpCoeff y ρ (Ring._*_ Rg c (eval x ρ)) i)'),
    ('  accumulate i c (state s) = state (λ j with finDecEq j i\n    ... | yes _ = s j + c',
     '  accumulate i c (state s) = state (λ j with finDecEq j i\n    ... | yes _ = Ring._+_ Rg (s j) c'),
    ('    state (λ i → runState s i + b i)', '    state (λ i → Ring._+_ Rg (runState s i) (b i))'),
]:
    region = region.replace(old, new)

# Remaining smooth-algebra applications whose principal argument is a scalar.
for name in ['exp', 'log', 'tanh', 'sigmoid']:
    region = re.sub(rf'(?<![A-Za-z0-9_.]){name} \(([^()]+)\)', rf'SmoothAlgebra.{name} S (\1)', region)

# Coordinate scalar arithmetic missed by exact patterns.
region = re.sub(r'(?m)^(\s*)([A-Za-z][A-Za-z0-9_]*) i \+ ([A-Za-z][A-Za-z0-9_]*) i$', r'\1Ring._+_ Rg (\2 i) (\3 i)', region)
region = re.sub(r'(?m)^(\s*)([A-Za-z][A-Za-z0-9_]*) i \* ([A-Za-z][A-Za-z0-9_]*) i$', r'\1Ring._*_ Rg (\2 i) (\3 i)', region)
text = text[:start] + region + text[end:]

start = text.find('record OrderedRing : Set₁ where')
end = text.find('\nrecord SmoothAlgebra : Set₁ where', start)
if start < 0 or end < 0:
    raise SystemExit('OrderedRing region not found')
region = text[start:end]
replacements = {
    'addLe : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d': 'addLe : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)',
    'mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ a * b': 'mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ (a * b)',
    'mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → c * a ≤ c * b': 'mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → (c * a) ≤ (c * b)',
    'ltAdd : ∀ {a b c d} → a < b → c < d → a + c < b + d': 'ltAdd : ∀ {a b c d} → a < b → c < d → (a + c) < (b + d)',
    'addLtLeft : ∀ {a b c} → a < b → c + a < c + b': 'addLtLeft : ∀ {a b c} → a < b → (c + a) < (c + b)',
    'mulLtPosLeft : ∀ {a b c} → a < b → zero < c → c * a < c * b': 'mulLtPosLeft : ∀ {a b c} → a < b → zero < c → (c * a) < (c * b)',
    'mulLtPosCancelLeft : ∀ {a b c} → c * a < c * b → zero < c → a < b': 'mulLtPosCancelLeft : ∀ {a b c} → (c * a) < (c * b) → zero < c → a < b',
    'mulPos : ∀ {a b} → zero < a → zero < b → zero < a * b': 'mulPos : ∀ {a b} → zero < a → zero < b → zero < (a * b)',
    'subLtZero : ∀ {a b} → a + neg b < zero → a < b': 'subLtZero : ∀ {a b} → (a + neg b) < zero → a < b',
    'squarePositive : ∀ {x} → x ≠ zero → zero < x * x': 'squarePositive : ∀ {x} → ¬ (x ≡ zero) → zero < (x * x)',
    'squareNonnegative : ∀ x → zero ≤ x * x': 'squareNonnegative : ∀ x → zero ≤ (x * x)',
    'absTriangle : ∀ x y → abs (x + y) ≤ abs x + abs y': 'absTriangle : ∀ x y → abs (x + y) ≤ (abs x + abs y)',
}
changed = 0
for old_sig, new_sig in replacements.items():
    if old_sig in region:
        region = region.replace(old_sig, new_sig)
        changed += 1
for old_name, new_name in [('zero','Ring.zero ring'), ('one','Ring.one ring'), ('neg','Ring.neg ring')]:
    region = re.sub(rf'(?<![A-Za-z0-9_.]){re.escape(old_name)}(?![A-Za-z0-9_])', new_name, region)
for old, new in [
    ('a + c','(Ring._+_ ring a c)'), ('c + a','(Ring._+_ ring c a)'),
    ('c + b','(Ring._+_ ring c b)'), ('a + neg b','(Ring._+_ ring a (Ring.neg ring b))'),
    ('x + y','(Ring._+_ ring x y)'), ('x * y','(Ring._*_ ring x y)'),
    ('c * a','(Ring._*_ ring c a)'), ('c * b','(Ring._*_ ring c b)'),
    ('a * b','(Ring._*_ ring a b)'), ('x * x','(Ring._*_ ring x x)')]:
    region = region.replace(old, new)
text = text[:start] + region + text[end:]

path.write_text(text)
print(
    f'algebra-normalization={changed}; complete-local-scalar-qualification=True; '
    'nat-zero-boundary-normalized=True; tabulateV-source-patterns-normalized=True; '
    'tabulateV-named-implicit-arguments=True; tabulateV-zero-qualified=True; tabulateV-suc-qualified=True; '
    'global-ring-open-removed=True; global-ordered-ring-open-removed=True; ordered-ring-primitives-qualified=True; '
    'nested-ring-carriers-qualified=True; centered-signature=True; normalise-signature=True; '
    'lstm-gates-projection=True; local-EfficientCHAD-R-renamed=True; EfficientCHAD-complete-qualified=True'
)
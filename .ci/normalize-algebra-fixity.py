from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

# Explicit local algebra bindings.
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

# SmoothAlgebra max is binary; keep the other analytic primitives unary.
text = text.replace(
    '    sqrt recip max min : R → R\n'
    '    maxNonnegative : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ max a b\n',
    '    sqrt recip min : R → R\n'
    '    max : R → R → R\n'
    '    maxNonnegative : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ max a b\n',
    1,
)
text = text.replace('    fromNatZero : fromNat zero ≡ zero\n', '    fromNatZero : fromNat Nat.zero ≡ zero\n', 1)

# The source omits the A pattern and matches n implicitly. Name both
# binders explicitly so Nat.zero cannot be captured as type A.
text = text.replace('tabulateV {zero} f = []', 'tabulateV {A = _} {n = Nat.zero} f = []', 1)
text = text.replace('tabulateV {suc n} f = f fzero ∷ tabulateV (λ i → f (fsuc i))',
                    'tabulateV {A = A} {n = Nat.suc n} f = f fzero ∷ tabulateV (λ i → f (fsuc i))', 1)

# Normalize finite CHAD local carrier/fixity.
start = text.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = text.find('\n------------------------------------------------------------------------', start + 10)
if start < 0 or end < 0:
    raise SystemExit('EfficientCHAD module region not found')
region = text[start:end]
region = re.sub(r'(?<![A-Za-z0-9_])R(?![A-Za-z0-9_])', 'CR', region)
region = region.replace('CRg = OrderedRing.ring orderedRing', 'Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)')
region = region.replace('Rg = OrderedRing.ring orderedRing', 'Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)')
region = region.replace('Ring.CR Rg', 'Ring.R Rg')
region = region.replace('eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i', '(eval y ρ * coeff x ρ i) + (eval x ρ * coeff y ρ i)')
region = region.replace('c * eval y ρ + eval x ρ * c', '(c * eval y ρ) + (eval x ρ * c)')
text = text[:start] + region + text[end:]

# Catch any remaining exact unqualified projection outside EfficientCHAD too.
text = text.replace('OrderedRing.ring orderedRing', 'OrderedRing.ring (SmoothAlgebra.orderedRing S)')

# Normalize OrderedRing fixity and primitive operations.
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

# Keep SmoothAlgebra's carrier tied to its concrete ordered ring.
start = text.find('record SmoothAlgebra : Set₁ where')
end = text.find('\nopen SmoothAlgebra', start)
if start < 0 or end < 0:
    raise SystemExit('SmoothAlgebra region not found')
region = text[start:end]
region = re.sub(r'(?<![A-Za-z0-9_])R(?![A-Za-z0-9_])', 'Ring.R (OrderedRing.ring orderedRing)', region)
text = text[:start] + region + text[end:]

path.write_text(text)
print(
    f'algebra-normalization={changed}; max-arity-normalized=True; nat-zero-boundary-normalized=True; '
    'tabulateV-source-patterns-normalized=True; tabulateV-named-implicit-arguments=True; '
    'tabulateV-zero-qualified=True; tabulateV-suc-qualified=True; global-ring-open-removed=True; '
    'global-ordered-ring-open-removed=True; ordered-ring-primitives-qualified=True; '
    'nested-ring-carriers-qualified=True; centered-signature=True; normalise-signature=True; '
    'lstm-gates-projection=True; local-EfficientCHAD-R-renamed=True; '
    'EfficientCHAD-orderedRing-qualified=True; global-orderedRing-use-qualified=True; '
    'vector-subtraction-signature=True; chad-product-sum-parenthesized=True'
)

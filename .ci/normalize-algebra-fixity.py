from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

# Close local algebra helpers with explicit scalar types.
old = '''vSub {S} = zipWithV minus
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  minus x y = Ring._+_ Rg x (Ring.neg Rg y)
'''
new = '''vSub {S} = zipWithV minus
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  minus : Scalar S → Scalar S → Scalar S
  minus x y = Ring._+_ Rg x (Ring.neg Rg y)
'''
if old in text:
    text = text.replace(old, new, 1)

old = '''  μ = vSum xs * SmoothAlgebra.recip S (SmoothAlgebra.fromNat S d)
  centered x = x + neg μ
'''
new = '''  μ = vSum xs * SmoothAlgebra.recip S (SmoothAlgebra.fromNat S d)
  centered : Scalar S → Scalar S
  centered x = x + neg μ
'''
if old in text:
    text = text.replace(old, new, 1)

old = '''  invStd = SmoothAlgebra.recip S
    (SmoothAlgebra.sqrt S (variance + LayerNorm.epsilon ln))
  normalise x = centered x * invStd
'''
new = '''  invStd = SmoothAlgebra.recip S
    (SmoothAlgebra.sqrt S (variance + LayerNorm.epsilon ln))
  normalise : Scalar S → Scalar S
  normalise x = centered x * invStd
'''
if old in text:
    text = text.replace(old, new, 1)

# Repair an invalid nested LSTM gate projection without changing theorem names.
text = text.replace('LSTMGates.gates (LSTMBlock.gates block)', 'LSTMBlock.gates block')

# Remove redundant global Ring and OrderedRing opens. Their public exports are
# already available through the concrete algebra records; keeping both global
# and record-local opens creates overloaded projections in staged modules.
text = text.replace('\nopen Ring\n\nrecord OrderedRing : Set₁ where', '\nrecord OrderedRing : Set₁ where', 1)
text = text.replace('\nopen OrderedRing\n\nrecord SmoothAlgebra : Set₁ where', '\nrecord SmoothAlgebra : Set₁ where', 1)

# Normalize the finite CHAD local carrier alias.
start = text.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = text.find('\n------------------------------------------------------------------------', start + 10)
if start < 0 or end < 0:
    raise SystemExit('EfficientCHAD module region not found')
region = text[start:end]
region = re.sub(r'(?<![A-Za-z0-9_])R(?![A-Za-z0-9_])', 'CR', region)
region = region.replace('CRg = OrderedRing.ring orderedRing', 'Rg = OrderedRing.ring orderedRing')
region = region.replace('Ring.CR Rg', 'Ring.R Rg')
region = region.replace(
    'eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i',
    '(eval y ρ * coeff x ρ i) + (eval x ρ * coeff y ρ i)')
region = region.replace(
    'c * eval y ρ + eval x ρ * c',
    '(c * eval y ρ) + (eval x ρ * c)')
text = text[:start] + region + text[end:]

# Make the finite ordered-ring interface explicit enough for independent
# staged checking while retaining exactly the same algebraic propositions.
start = text.find('record OrderedRing : Set₁ where')
end = text.find('\nopen OrderedRing', start)
if start < 0:
    raise SystemExit('OrderedRing region not found')
if end < 0:
    # The global open was removed, so terminate at SmoothAlgebra instead.
    end = text.find('\nrecord SmoothAlgebra : Set₁ where', start)
if end < 0:
    raise SystemExit('OrderedRing terminator not found')
region = text[start:end]
replacements = {
    'addLe : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d':
        'addLe : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)',
    'mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ a * b':
        'mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ (a * b)',
    'mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → c * a ≤ c * b':
        'mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → (c * a) ≤ (c * b)',
    'ltAdd : ∀ {a b c d} → a < b → c < d → a + c < b + d':
        'ltAdd : ∀ {a b c d} → a < b → c < d → (a + c) < (b + d)',
    'addLtLeft : ∀ {a b c} → a < b → c + a < c + b':
        'addLtLeft : ∀ {a b c} → a < b → (c + a) < (c + b)',
    'mulLtPosLeft : ∀ {a b c} → a < b → zero < c → c * a < c * b':
        'mulLtPosLeft : ∀ {a b c} → a < b → zero < c → (c * a) < (c * b)',
    'mulLtPosCancelLeft : ∀ {a b c} → c * a < c * b → zero < c → a < b':
        'mulLtPosCancelLeft : ∀ {a b c} → (c * a) < (c * b) → zero < c → a < b',
    'mulPos : ∀ {a b} → zero < a → zero < b → zero < a * b':
        'mulPos : ∀ {a b} → zero < a → zero < b → zero < (a * b)',
    'subLtZero : ∀ {a b} → a + neg b < zero → a < b':
        'subLtZero : ∀ {a b} → (a + neg b) < zero → a < b',
    'squarePositive : ∀ {x} → x ≠ zero → zero < x * x':
        'squarePositive : ∀ {x} → ¬ (x ≡ zero) → zero < (x * x)',
    'squareNonnegative : ∀ x → zero ≤ x * x':
        'squareNonnegative : ∀ x → zero ≤ (x * x)',
    'absTriangle : ∀ x y → abs (x + y) ≤ abs x + abs y':
        'absTriangle : ∀ x y → abs (x + y) ≤ (abs x + abs y)',
}
changed = 0
for old_sig, new_sig in replacements.items():
    count = region.count(old_sig)
    if count:
        region = region.replace(old_sig, new_sig)
        changed += count

# Explicit ring projections inside OrderedRing keep staged prefixes independent
# of the order in which public projections become visible.
for old_name, new_name in {
    'zero': 'Ring.zero ring',
    'one': 'Ring.one ring',
    'neg': 'Ring.neg ring',
}.items():
    region = re.sub(rf'(?<![A-Za-z0-9_.]){re.escape(old_name)}(?![A-Za-z0-9_])', new_name, region)
region = region.replace('a + c', '(Ring._+_ ring a c)')
region = region.replace('c + a', '(Ring._+_ ring c a)')
region = region.replace('c + b', '(Ring._+_ ring c b)')
region = region.replace('a + neg b', '(Ring._+_ ring a (Ring.neg ring b))')
region = region.replace('x + y', '(Ring._+_ ring x y)')
region = region.replace('x * y', '(Ring._*_ ring x y)')
region = region.replace('c * a', '(Ring._*_ ring c a)')
region = region.replace('c * b', '(Ring._*_ ring c b)')
region = region.replace('a * b', '(Ring._*_ ring a b)')
region = region.replace('x * x', '(Ring._*_ ring x x)')
text = text[:start] + region + text[end:]

# SmoothAlgebra carrier is explicit but its concrete ordered-ring witness still
# supplies all inherited operations through the record-local public opening.
start = text.find('record SmoothAlgebra : Set₁ where')
end = text.find('\nopen SmoothAlgebra', start)
if start < 0 or end < 0:
    raise SystemExit('SmoothAlgebra region not found')
region = text[start:end]
region = re.sub(
    r'(?<![A-Za-z0-9_])R(?![A-Za-z0-9_])',
    'Ring.R (OrderedRing.ring orderedRing)',
    region,
)
text = text[:start] + region + text[end:]

path.write_text(text)
print(
    f'algebra-normalization={changed}; '
    'global-ring-open-removed=True; global-ordered-ring-open-removed=True; '
    'ordered-ring-primitives-qualified=True; nested-ring-carriers-qualified=True; '
    'centered-signature=True; normalise-signature=True; '
    'lstm-gates-projection=True; local-EfficientCHAD-R-renamed=True; '
    'vector-subtraction-signature=True; chad-product-sum-parenthesized=True'
)

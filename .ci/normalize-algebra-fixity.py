from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

# Close the local subtraction helper explicitly.
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

# The global `open Ring` exposes Ring.R. Alpha-rename only the local alias
# in EfficientCHAD so --safe accepts the nested declaration.
start = text.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = text.find('\n------------------------------------------------------------------------', start + 10)
if start < 0 or end < 0:
    raise SystemExit('EfficientCHAD module region not found')
region = text[start:end]
region = re.sub(r'(?<![A-Za-z0-9_])R(?![A-Za-z0-9_])', 'CR', region)
region = region.replace('CRg = OrderedRing.ring orderedRing', 'Rg = OrderedRing.ring orderedRing')
region = region.replace('Ring.CR Rg', 'Ring.R Rg')
text = text[:start] + region + text[end:]

# Normalize mixed arithmetic/comparison precedence only inside OrderedRing.
start = text.find('record OrderedRing : Set₁ where')
end = text.find('\nopen OrderedRing', start)
if start < 0 or end < 0:
    raise SystemExit('OrderedRing region not found')
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
path.write_text(text[:start] + region + text[end:])
print(f'algebra-normalization={changed}; local-EfficientCHAD-R-renamed=True; vector-subtraction-signature=True')

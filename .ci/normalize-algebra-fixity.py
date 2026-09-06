from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
if 'infix 4 _≤_ _<_' in text or 'infixl 30 _*_' in text:
    text = text.replace('infix 4 _≤_ _<_\ninfixl 20 _+_\ninfixl 30 _*_\n\n', '', 1)
fixes = {
    'addLe : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d':
        'addLe : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)',
    'mulNonneg : ∀ {a b} → zero ≤ a * b':
        'mulNonneg : ∀ {a b} → zero ≤ (a * b)',
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
    'subLtZero : ∀ {a b} → a + neg b < zero → a < b':
        'subLtZero : ∀ {a b} → (a + neg b) < zero → a < b',
}
for old, new in fixes.items():
    if old not in text:
        raise SystemExit(f'expected algebra expression not found: {old}')
    text = text.replace(old, new, 1)
text = text.replace('absTriangle : ∀ x y → abs (x + y) ≤ abs x + abs y',
                    'absTriangle : ∀ x y → abs (x + y) ≤ (abs x + abs y)', 1)
text = text.replace('squarePositive : ∀ {x} → x ≠ zero → zero < x * x',
                    'squarePositive : ∀ {x} → x ≠ zero → zero < (x * x)', 1)
text = text.replace('squareNonnegative : ∀ x → zero ≤ x * x',
                    'squareNonnegative : ∀ x → zero ≤ (x * x)', 1)
path.write_text(text)
print('mixed-order-expressions-parenthesized=True')

from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

exact = {
    '    mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ a * b':
        '    mulNonneg : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ Ring._*_ ring a b',
    '    mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → c * a ≤ c * b':
        '    mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → Ring._*_ ring c a ≤ Ring._*_ ring c b',
    '    mulPos : ∀ {a b} → zero < a → zero < b → zero < a * b':
        '    mulPos : ∀ {a b} → zero < a → zero < b → zero < Ring._*_ ring a b',
    '    squarePositive : ∀ {x} → x ≠ zero → zero < x * x':
        '    squarePositive : ∀ {x} → x ≠ zero → zero < Ring._*_ ring x x',
    '    squareNonnegative : ∀ x → zero ≤ x * x':
        '    squareNonnegative : ∀ x → zero ≤ Ring._*_ ring x x',
}

changed = 0
for old, new in exact.items():
    if old in text:
        text = text.replace(old, new)
        changed += 1

path.write_text(text)
print(f'final-ordered-field-qualification={changed}')

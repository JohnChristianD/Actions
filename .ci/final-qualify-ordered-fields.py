from pathlib import Path
import re

# Final deterministic qualification pass for the CompleteSafe OrderedRing surface.
p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
start = s.index('record OrderedRing')
end = s.index('\n------------------------------------------------------------------------', start)
segment = s[start:end]

segment = segment.replace(
    '    mulNonneg : ∀ {a b} → zero ≤ a * b\n',
    '    mulNonneg : ∀ {a b} → zero ≤ Ring._*_ ring a b\n',
    1,
)
segment = segment.replace(
    '    mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → c * a ≤ c * b\n',
    '    mulLeLeft : ∀ {a b c} → a ≤ b → zero ≤ c → Ring._*_ ring c a ≤ Ring._*_ ring c b\n',
    1,
)
segment = segment.replace(
    '    mulLtPosLeft : ∀ {a b c} → a < b → zero < c → c * a < c * b\n',
    '    mulLtPosLeft : ∀ {a b c} → a < b → zero < c → Ring._*_ ring c a < Ring._*_ ring c b\n',
    1,
)
segment = segment.replace(
    '    mulLtPosCancelLeft : ∀ {a b c} → c * a < c * b → zero < c → a < b\n',
    '    mulLtPosCancelLeft : ∀ {a b c} → Ring._*_ ring c a < Ring._*_ ring c b → zero < c → a < b\n',
    1,
)
segment = segment.replace(
    '    mulPos : ∀ {a b} → zero < a → zero < b → zero < a * b\n',
    '    mulPos : ∀ {a b} → zero < a → zero < b → zero < Ring._*_ ring a b\n',
    1,
)
segment = segment.replace(
    '    squarePositive : ∀ {x} → x ≠ zero → zero < x * x\n',
    '    squarePositive : ∀ {x} → x ≠ zero → zero < Ring._*_ ring x x\n',
    1,
)
segment = segment.replace(
    '    squareNonnegative : ∀ x → zero ≤ x * x\n',
    '    squareNonnegative : ∀ x → zero ≤ Ring._*_ ring x x\n',
    1,
)

segment = segment.replace(
    '    addLe : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d\n',
    '    addLe : ∀ {a b c d} → a ≤ b → c ≤ d → Ring._+_ ring a c ≤ Ring._+_ ring b d\n',
    1,
)
segment = segment.replace(
    '    ltAdd : ∀ {a b c d} → a < b → c < d → a + c < b + d\n',
    '    ltAdd : ∀ {a b c d} → a < b → c < d → Ring._+_ ring a c < Ring._+_ ring b d\n',
    1,
)
segment = segment.replace(
    '    addLtLeft : ∀ {a b c} → a < b → c + a < c + b\n',
    '    addLtLeft : ∀ {a b c} → a < b → Ring._+_ ring c a < Ring._+_ ring c b\n',
    1,
)

s = s[:start] + segment + s[end:]
p.write_text(s)

for forbidden in (
    'zero ≤ a * b',
    'a + c ≤ b + d',
    'c * a ≤ c * b',
    'a < b → c < d → a + c < b + d',
    'a < b → c + a < c + b',
    'zero < a * b',
    'zero < x * x',
):
    if forbidden in segment:
        raise SystemExit(f'ordered-field qualification incomplete: {forbidden!r}')

for line in segment.splitlines():
    if any(k in line for k in ('mulNonneg', 'mulLeLeft', 'mulLtPosLeft', 'mulLtPosCancelLeft', 'mulPos', 'squarePositive', 'squareNonnegative')):
        print('ORDERED-RING-PRODUCT:', line)
print('final-ordered-ring-qualification=validated')

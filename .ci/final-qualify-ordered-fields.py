from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
start = s.index('record OrderedRing')
end = s.index('\n------------------------------------------------------------------------', start)
segment = s[start:end]

# OrderedRing is checked while both Ring and Nat parsing environments are live.
# Qualify arithmetic that belongs to Ring so Agda cannot choose two identical
# grammar declarations for + or *.
exact = [
    ('a + c ≤ b + d', 'Ring._+_ ring a c ≤ Ring._+_ ring b d'),
    ('a + neg b < zero', 'Ring._+_ ring a (neg b) < zero'),
    ('zero < a * b', 'zero < Ring._*_ ring a b'),
    ('zero ≤ a * b', 'zero ≤ Ring._*_ ring a b'),
    ('c * a ≤ c * b', 'Ring._*_ ring c a ≤ Ring._*_ ring c b'),
    ('c * a < c * b', 'Ring._*_ ring c a < Ring._*_ ring c b'),
    ('a * e < b * d', 'Ring._*_ ring a e < Ring._*_ ring b d'),
    ('zero < x * x', 'zero < Ring._*_ ring x x'),
    ('zero ≤ x * x', 'zero ≤ Ring._*_ ring x x'),
    ('a < b → c < d → a + c < b + d',
     'a < b → c < d → Ring._+_ ring a c < Ring._+_ ring b d'),
    ('a < b → c + a < c + b',
     'a < b → Ring._+_ ring c a < Ring._+_ ring c b'),
    ('abs (x + y) ≤ abs x + abs y',
     'abs (Ring._+_ ring x y) ≤ Ring._+_ ring (abs x) (abs y)'),
    ('abs (x * y) ≡ abs x * abs y',
     'abs (Ring._*_ ring x y) ≡ Ring._*_ ring (abs x) (abs y)'),
]
for old, new in exact:
    segment = segment.replace(old, new)

# Catch the two ordered addition/multiplication implication forms without
# changing Ring field declarations that are already parenthesized.
segment = re.sub(
    r'(?m)^(\s*ltAdd\s*:\s*∀ \{a b c d\} → )a < b → c < d → a \+ c < b \+ d$',
    r'\1a < b → c < d → Ring._+_ ring a c < Ring._+_ ring b d',
    segment,
)
segment = re.sub(
    r'(?m)^(\s*addLtLeft\s*:\s*∀ \{a b c\} → )a < b → c \+ a < c \+ b$',
    r'\1a < b → Ring._+_ ring c a < Ring._+_ ring c b',
    segment,
)

s = s[:start] + segment + s[end:]
p.write_text(s)

for forbidden in (
    'a + c ≤ b + d',
    'a + neg b < zero',
    'zero < a * b',
    'zero ≤ a * b',
    'c * a ≤ c * b',
    'c * a < c * b',
    'a * e < b * d',
    'zero < x * x',
    'zero ≤ x * x',
    'a < b → c < d → a + c < b + d',
    'a < b → c + a < c + b',
    'abs (x + y) ≤ abs x + abs y',
    'abs (x * y) ≡ abs x * abs y',
):
    if forbidden in segment:
        raise SystemExit(f'ordered-field qualification incomplete: {forbidden!r}')

print('final-ordered-ring-qualification=validated')

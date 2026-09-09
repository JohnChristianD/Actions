from pathlib import Path

# Deterministic parser normalization for the CompleteSafe OrderedRing boundary.
p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
start = s.index('record OrderedRing')
end = s.index('\n------------------------------------------------------------------------', start)
segment = s[start:end]

replacements = (
    ('zero ≤ a * b', 'zero ≤ Ring._*_ ring a b'),
    ('c * a ≤ c * b', 'Ring._*_ ring c a ≤ Ring._*_ ring c b'),
    ('c * a < c * b', 'Ring._*_ ring c a < Ring._*_ ring c b'),
    ('zero < a * b', 'zero < Ring._*_ ring a b'),
    ('zero < x * x', 'zero < Ring._*_ ring x x'),
    ('zero ≤ x * x', 'zero ≤ Ring._*_ ring x x'),
    ('a + c ≤ b + d', 'Ring._+_ ring a c ≤ Ring._+_ ring b d'),
    ('a + c < b + d', 'Ring._+_ ring a c < Ring._+_ ring b d'),
    ('c + a < c + b', 'Ring._+_ ring c a < Ring._+_ ring c b'),
    ('a + neg b < zero', 'Ring._+_ ring a (neg b) < zero'),
    ('abs (x + y) ≤ abs x + abs y', 'abs (Ring._+_ ring x y) ≤ Ring._+_ ring (abs x) (abs y)'),
)
for old, new in replacements:
    segment = segment.replace(old, new)

s = s[:start] + segment + s[end:]

needle = '  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)\n  minus x y = Ring._+_ Rg x (Ring.neg Rg y)\n'
if needle in s and '  minus : Ring.R Rg → Ring.R Rg → Ring.R Rg\n' not in s:
    s = s.replace(needle, '  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)\n  minus : Ring.R Rg → Ring.R Rg → Ring.R Rg\n  minus x y = Ring._+_ Rg x (Ring.neg Rg y)\n', 1)

p.write_text(s)

for forbidden in (
    'zero ≤ a * b', 'c * a ≤ c * b', 'c * a < c * b',
    'zero < a * b', 'zero < x * x', 'zero ≤ x * x',
    'a + c ≤ b + d', 'a + c < b + d', 'c + a < c + b',
    'a + neg b < zero', 'abs (x + y) ≤ abs x + abs y',
):
    if forbidden in segment:
        raise SystemExit(f'ordered-field qualification incomplete: {forbidden!r}')
print('final-ordered-ring-qualification=validated')
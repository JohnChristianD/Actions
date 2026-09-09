from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
start = s.index('record OrderedRing')
end = s.index('\n------------------------------------------------------------------------', start)
segment = s[start:end]

# Within OrderedRing, qualify every arithmetic expression that would otherwise
# share grammar with Agda.Builtin.Nat operators.
repls = [
    (r'zero ≤ a \* b', 'zero ≤ Ring._*_ ring a b'),
    (r'c \* a ≤ c \* b', 'Ring._*_ ring c a ≤ Ring._*_ ring c b'),
    (r'a \* e < b \* d', 'Ring._*_ ring a e < Ring._*_ ring b d'),
    (r'c \* a < c \* b', 'Ring._*_ ring c a < Ring._*_ ring c b'),
    (r'zero < a \* b', 'zero < Ring._*_ ring a b'),
    (r'zero < x \* x', 'zero < Ring._*_ ring x x'),
    (r'zero ≤ x \* x', 'zero ≤ Ring._*_ ring x x'),
    (r'a \+ c ≤ b \+ d', 'Ring._+_ ring a c ≤ Ring._+_ ring b d'),
    (r'a < b → c < d → a \+ c < b \+ d', 'a < b → c < d → Ring._+_ ring a c < Ring._+_ ring b d'),
    (r'a < b → c \+ a < c \+ b', 'a < b → Ring._+_ ring c a < Ring._+_ ring c b'),
]
for pattern, repl in repls:
    segment = re.sub(pattern, repl, segment)

# OrderedRing itself needs no unqualified Nat arithmetic. Ring field syntax
# remains deliberately qualified only where required by parser ambiguity.
s = s[:start] + segment + s[end:]
p.write_text(s)

for forbidden in (
    'zero ≤ a * b',
    'c * a ≤ c * b',
    'c * a < c * b',
    'zero < a * b',
    'zero < x * x',
    'zero ≤ x * x',
    'a + c ≤ b + d',
    'a < b → c < d → a + c < b + d',
    'a < b → c + a < c + b',
):
    if forbidden in segment:
        raise SystemExit(f'ordered-field qualification incomplete: {forbidden!r}')

print('final-ordered-ring-qualification=validated')

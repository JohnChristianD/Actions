from pathlib import Path
import re

# Final deterministic qualification pass for the CompleteSafe OrderedRing surface.
p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
start = s.index('record OrderedRing')
end = s.index('\n------------------------------------------------------------------------', start)
segment = s[start:end]

segment = re.sub(
    r'(mulNonneg\s*:\s*[^\n]*→\s*zero ≤ )a \* b',
    r'\1Ring._*_ ring a b',
    segment,
)
segment = re.sub(
    r'(mulLeLeft\s*:\s*[^\n]*→\s*zero ≤ c → )c \* a ≤ c \* b',
    r'\1Ring._*_ ring c a ≤ Ring._*_ ring c b',
    segment,
)
segment = re.sub(
    r'(mulLtPosLeft\s*:\s*[^\n]*→\s*zero < c → )c \* a < c \* b',
    r'\1Ring._*_ ring c a < Ring._*_ ring c b',
    segment,
)
segment = re.sub(
    r'(mulLtPosCancelLeft\s*:\s*[^\n]*→\s*)c \* a < c \* b',
    r'\1Ring._*_ ring c a < Ring._*_ ring c b',
    segment,
)
segment = re.sub(
    r'(mulPos\s*:\s*[^\n]*→\s*zero < a \) → zero < )a \* b',
    r'\1Ring._*_ ring a b',
    segment,
)
segment = re.sub(
    r'(squarePositive\s*:\s*[^\n]*→\s*zero < )x \* x',
    r'\1Ring._*_ ring x x',
    segment,
)
segment = re.sub(
    r'(squareNonnegative\s*:\s*[^\n]*→\s*zero ≤ )x \* x',
    r'\1Ring._*_ ring x x',
    segment,
)

# The outer open Ring and the nested open Ring ring expose the same infix +
# twice to the parser. Qualify additive ordered-field fields explicitly.
segment = segment.replace(
    'a + c ≤ b + d',
    'Ring._+_ ring a c ≤ Ring._+_ ring b d',
    1,
)
segment = segment.replace(
    'a < b → c < d → a + c < b + d',
    'a < b → c < d → Ring._+_ ring a c < Ring._+_ ring b d',
    1,
)
segment = segment.replace(
    'a < b → c + a < c + b',
    'a < b → Ring._+_ ring c a < Ring._+_ ring c b',
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
):
    if forbidden in segment:
        raise SystemExit(f'final ordered-field qualification incomplete: {forbidden!r}')

print('final-ordered-ring-qualification=validated')
for line in segment.splitlines():
    if 'squarePositive' in line or 'squareNonnegative' in line:
        print('ORDERED-RING-SQUARE:', line)

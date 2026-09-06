from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('record OrderedRing : Set₁ where')
end = text.find('\nopen OrderedRing', start)
if start < 0 or end < 0:
    raise SystemExit('OrderedRing region not found')
region = text[start:end]

# Only rewrite arithmetic appearing inside comparison expressions in OrderedRing.
# This avoids touching arbitrary algebraic terms elsewhere and is idempotent.
lines = []
changed = 0
for line in region.splitlines(True):
    if '≤' not in line and '<' not in line:
        lines.append(line)
        continue
    original = line
    # Parenthesize products used as operands of ≤ or <.
    line = re.sub(r'(?<!\()[A-Za-z_][A-Za-z0-9_\']* \* [A-Za-z_][A-Za-z0-9_\']*(?!\))',
                  lambda m: '(' + m.group(0) + ')', line)
    # Parenthesize sums used as operands of ≤ or < when not already grouped.
    line = re.sub(r'(?<!\()[A-Za-z_][A-Za-z0-9_\']*(?: + neg [A-Za-z_][A-Za-z0-9_\']*| + [A-Za-z_][A-Za-z0-9_\']*) (?=≤|<)',
                  lambda m: '(' + m.group(0).rstrip() + ') ', line)
    if line != original:
        changed += 1
    lines.append(line)
region2 = ''.join(lines)
path.write_text(text[:start] + region2 + text[end:])
print(f'ordered-ring-comparison-normalized={changed > 0}; lines={changed}')

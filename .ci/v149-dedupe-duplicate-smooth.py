from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = '------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n'
vector = '------------------------------------------------------------------------\n-- Canonical vector algebra\n'
count = s.count(marker)
if count > 1:
    first = s.index(marker)
    second = s.find(marker, first + len(marker))
    end = s.find(vector, second)
    if end < 0:
        raise SystemExit('duplicate SmoothAlgebra block terminator not found')
    s = s[:second] + s[end:]
if s.count('record SmoothAlgebra : Set₁ where') != 1:
    raise SystemExit('SmoothAlgebra definition count is not one after dedupe')
p.write_text(s)
print('smooth-algebra-definition-count=1')

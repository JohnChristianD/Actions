from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
record = 'record SmoothAlgebra : Set₁ where'
vector = '------------------------------------------------------------------------\n-- Canonical vector algebra\n'
count = s.count(record)
if count > 1:
    first = s.index(record)
    second = s.find(record, first + len(record))
    end = s.find(vector, second)
    if end < 0:
        raise SystemExit('duplicate SmoothAlgebra terminator not found')
    s = s[:second] + s[end:]
if s.count(record) != 1:
    raise SystemExit(f'SmoothAlgebra definition count is {s.count(record)}, expected 1')
p.write_text(s)
print('smooth-algebra-definition-count=1')
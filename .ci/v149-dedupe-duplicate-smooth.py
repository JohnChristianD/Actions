from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
record = 'record SmoothAlgebra : Set₁ where'
second = s.find(record, s.find(record) + len(record))
if second >= 0:
    keep = s.find('vAddZeroL :', second)
    if keep < 0:
        raise SystemExit('vAddZeroL terminator not found after duplicate SmoothAlgebra')
    s = s[:second] + s[keep:]
if s.count(record) != 1:
    raise SystemExit(f'SmoothAlgebra definition count is {s.count(record)}, expected 1')
p.write_text(s)
print('smooth-algebra-definition-count=1')
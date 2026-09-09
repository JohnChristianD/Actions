from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old = '''residualSquareNonzero_v140 : ∀ {S}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →'''
new = '''residualSquareNonzero_v140 : ∀ {S : SmoothAlgebra}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →'''
count = s.count(old)
if count > 1:
    raise SystemExit(f'non-unique residual carrier signature: {count}')
if count == 1:
    s = s.replace(old, new, 1)
    p.write_text(s)
    print('residual theorem carrier made explicit exactly once')
else:
    print('residual theorem carrier already explicit or normalized away')

from pathlib import Path
p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old = '    denominatorDomain : VecS S d → SmoothAlgebra.sqrtDomain S (layerNormVariance epsilon)\n  where\n  layerNormVariance : Scalar S → Scalar S\n  layerNormVariance eps = eps\n'
new = '    denominatorDomain : (xs : VecS S d) →\n      SmoothAlgebra.sqrtDomain S (layerNormVariance xs epsilon)\n'
if s.count(old) == 1:
    s = s.replace(old, new, 1)
elif s.count(new) != 1:
    raise SystemExit('LayerNorm malformed denominator-domain block not found uniquely')
p.write_text(s)
print('LayerNorm denominatorDomain normalized exactly once')

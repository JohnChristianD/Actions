from pathlib import Path
p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old_field = '    denominatorDomain : VecS S d → SmoothAlgebra.sqrtDomain S (layerNormVariance epsilon)\n  where\n  layerNormVariance : Scalar S → Scalar S\n  layerNormVariance eps = eps\n'
new_field = '    denominatorDomain : (xs : VecS S d) →\n      SmoothAlgebra.sqrtDomain S (layerNormVariance xs epsilon)\n'
if s.count(old_field) == 1:
    s = s.replace(old_field, new_field, 1)
elif s.count(new_field) != 1:
    raise SystemExit('LayerNorm denominator-domain malformed block not found uniquely')
p.write_text(s)
print('LayerNorm denominatorDomain now carries the actual variance denominator for each input')

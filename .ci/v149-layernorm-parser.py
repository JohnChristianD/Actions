from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

old = '    denominatorDomain : VecS S d → SmoothAlgebra.sqrtDomain S (layerNormVariance epsilon)\n  where\n  layerNormVariance : Scalar S → Scalar S\n  layerNormVariance eps = eps\n'
new = '    denominatorDomain : (xs : VecS S d) →\n      SmoothAlgebra.sqrtDomain S (layerNormVariance xs epsilon)\n'

if s.count(old) == 1:
    s = s.replace(old, new, 1)
    print('LayerNorm denominatorDomain normalized exactly once')
elif s.count('    denominatorDomain :') >= 1:
    print('LayerNorm denominatorDomain already has a scoped declaration')
else:
    raise SystemExit('LayerNorm denominator-domain declaration not found')

p.write_text(s)

from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

old = '''    denominatorDomain : VecS S d → SmoothAlgebra.sqrtDomain S (layerNormVariance epsilon)
  where
  layerNormVariance : Scalar S → Scalar S
  layerNormVariance eps = eps
'''
new = '''    denominatorDomain : (xs : VecS S d) →
      SmoothAlgebra.sqrtDomain S (layerNormVariance xs epsilon)
'''
if old in s:
    s = s.replace(old, new, 1)
elif 'denominatorDomain : (xs : VecS S d) →\n      SmoothAlgebra.sqrtDomain S (layerNormVariance xs epsilon)\n' not in s:
    raise SystemExit('LayerNorm malformed denominator-domain block not found uniquely')

# Agda does not make later top-level declarations visible at an earlier
# declaration site. Move the canonical mean/variance definitions above the
# LayerNorm record while keeping the inv-root theorem below the record.
record_marker = 'record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where\n'
mean_marker = 'layerNormMean : ∀ {S d} → VecS S d → Scalar S\n'
inv_marker = 'layerNormInvRootLaw : ∀ {S d} (ln : LayerNorm S d) (xs : VecS S d) →\n'
if record_marker not in s:
    raise SystemExit('LayerNorm record marker missing')
if mean_marker not in s or inv_marker not in s:
    raise SystemExit('canonical LayerNorm mean/variance block markers missing')
record_pos = s.index(record_marker)
mean_pos = s.index(mean_marker, record_pos)
inv_pos = s.index(inv_marker, mean_pos)
block = s[mean_pos:inv_pos]
s = s[:mean_pos] + s[inv_pos:]
record_pos = s.index(record_marker)
s = s[:record_pos] + block + s[record_pos:]

if s.index(mean_marker) > s.index(record_marker):
    raise SystemExit('layerNormMean remains below LayerNorm record')
if s.index(inv_marker) < s.index(record_marker):
    raise SystemExit('layerNormInvRootLaw moved above LayerNorm record')

p.write_text(s)
print('LayerNorm denominatorDomain normalized and mean/variance definitions ordered before record')

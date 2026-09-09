from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()

old = '''record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where
  field
    gain shift : VecS S d
    epsilon : Scalar S
    epsilonNonzero : epsilon ≠ Ring.zero (OrderedRing.base (SmoothAlgebra.orderedRing S))
    denominatorDomain : VecS S d → SmoothAlgebra.sqrtDomain S (layerNormVariance epsilon)
  where
  layerNormVariance : Scalar S → Scalar S
  layerNormVariance eps = eps
'''

new = '''record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where
  field
    gain shift : VecS S d
    epsilon : Scalar S
    epsilonNonzero : epsilon ≠ Ring.zero (OrderedRing.base (SmoothAlgebra.orderedRing S))
    denominatorDomain : VecS S d → SmoothAlgebra.sqrtDomain S epsilon
'''

if text.count(old) != 1:
    raise SystemExit('LayerNorm local-where parser pattern count mismatch')

text = text.replace(old, new, 1)
path.write_text(text)
print('LayerNorm domain binder moved to record-field scope exactly once')

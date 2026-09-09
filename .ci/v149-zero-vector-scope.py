from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = 'vAddZeroL : ∀ {S n} (x : VecS S n) (i : Fin n) →'
if marker not in s:
    raise SystemExit('vAddZeroL marker not found')
if 'zeroVector : ∀ {S n} → VecS S n\n' not in s:
    block = '''zeroVector : ∀ {S n} → VecS S n
zeroVector {S} {zero} = []
zeroVector {S} {suc n} =
  Ring.zero (OrderedRing.base (SmoothAlgebra.orderedRing S)) ∷ zeroVector {S = S} {n = n}

'''
    s = s.replace(marker, block + marker, 1)
# Remove the old local declaration, since the theorem type needs the shared one.
old = '''  where
  zeroVector : ∀ {S n} → VecS S n
  zeroVector {S} {zero} = []
  zeroVector {S} {suc n} =
    Ring.zero (OrderedRing.base (SmoothAlgebra.orderedRing S)) ∷ zeroVector {S = S} {n = n}
'''
s = s.replace(old, '', 1)
p.write_text(s)
if s.count('zeroVector : ∀ {S n} → VecS S n') != 1:
    raise SystemExit('zeroVector scope normalization count mismatch')
print('zeroVector-scope=top-level')

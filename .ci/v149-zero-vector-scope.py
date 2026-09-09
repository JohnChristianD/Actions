from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = 'vAddZeroL : ∀ {S n} (x : VecS S n) (i : Fin n) →'
if marker not in s:
    raise SystemExit('vAddZeroL marker not found')

name = 'zeroVectorTop'
if f'{name} : ∀ {{S n}} → VecS S n\n' not in s:
    block = '''zeroVectorTop : ∀ {S n} → VecS S n
zeroVectorTop {S} {zero} = []
zeroVectorTop {S} {suc n} =
  Ring.zero (OrderedRing.base (SmoothAlgebra.orderedRing S)) ∷ zeroVectorTop {S = S} {n = n}

'''
    s = s.replace(marker, block + marker, 1)

type_line = '  indexV (vAdd (zeroVector {S = S} {n = n}) x) i ≡ indexV x i'
if type_line in s:
    s = s.replace(type_line, '  indexV (vAdd (zeroVectorTop {S = S} {n = n}) x) i ≡ indexV x i', 1)
p.write_text(s)
if s.count(f'{name} : ∀ {{S n}} → VecS S n') != 1:
    raise SystemExit('zeroVectorTop declaration count mismatch')
if 'indexV (vAdd (zeroVectorTop {S = S} {n = n}) x) i' not in s:
    raise SystemExit('zeroVectorTop theorem type rewrite missing')
print('zeroVector-scope=top-level-unambiguous')
from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = path.read_text()
old = '  centered x = x + neg μ\n'
new = '''  centered : Scalar S → Scalar S
  centered x = Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x
    (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) μ)
'''
if old not in s:
    raise SystemExit('untyped centered helper not found')
s = s.replace(old, new, 1)
old2 = '  normalise x = centered x * invStd\n'
new2 = '''  normalise : Scalar S → Scalar S
  normalise x = Ring._*_ (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (centered x) invStd
'''
if old2 in s:
    s = s.replace(old2, new2, 1)
path.write_text(s)
print('layernorm centered/normalise helper signatures normalized')

from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = 'reciprocalNonnegative_v146 {S} {d} hd with'
start = s.find(marker)
if start < 0:
    raise SystemExit('reciprocalNonnegative_v146 theorem marker not found')
end = s.find('\n------------------------------------------------------------------------', start)
if end < 0:
    raise SystemExit('reciprocalNonnegative_v146 separator not found')
replacement = '''reciprocalNonnegative_v146 {S} {d} hd with
  ltDec (SmoothAlgebra.orderedRing S)
    (SmoothAlgebra.recip S d) zero
... | yes hneg =
  ⊥-elim
    (OrderedRing.notLtFromLe
      (OrderedRing.ltLe (OrderedRing.zeroLtOne
        {orderedRing = SmoothAlgebra.orderedRing S}))
      (trans
        (sym (SmoothAlgebra.reciprocalLaw S hd))
        (trans
          (OrderedRing.mulLtPosLeft hneg hd)
          (Ring.mulZeroR
            (OrderedRing.ring (SmoothAlgebra.orderedRing S)) d))))
... | no h = h
'''
s = s[:start] + replacement + s[end:]
if s.count(marker) != 1:
    raise SystemExit('reciprocal theorem normalization is not unique')
p.write_text(s)
print('reciprocal nonnegative theorem normalized exactly once')

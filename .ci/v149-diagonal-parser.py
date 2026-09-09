from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = 'diagonalNewtonExposurePositive_v146 h ='
start = s.find(marker)
if start < 0:
    raise SystemExit('diagonal exposure theorem marker not found')
sep = s.find('\n------------------------------------------------------------------------', start)
if sep < 0:
    raise SystemExit('diagonal exposure theorem boundary not found')
replacement = '''diagonalNewtonExposurePositive_v146 h =
  let OR = SmoothAlgebra.orderedRing _
      Rg = OrderedRing.ring OR
      t = SmoothAlgebra.recip _ (traceProduct_v146 h)
      htrace = OrderedRing.mulPos
        (CoupledHyperParameters_v146.gammaPositive h)
        (CoupledHyperParameters_v146.lambdaPositive h)
      hrec = reciprocalNonnegative_v146 htrace
      hlt = OrderedRing.addLtLeft
        (OrderedRing.zeroLtOne {orderedRing = OR}) t
      hlt' = trans (Ring.addZeroR Rg t) hlt
      hsum = OrderedRing.leLt hrec hlt'
  in trans
       (sym (Ring.addComm Rg t (Ring.one Rg)))
       hsum
'''
s = s[:start] + replacement + s[sep:]
p.write_text(s)
print('diagonal exposure proof normalized exactly once')

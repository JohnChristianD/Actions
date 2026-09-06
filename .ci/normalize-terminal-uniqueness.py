from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
start = s.find(marker)
if start < 0:
    raise SystemExit('expected qTerminalProjectionUnique theorem body not found')
sep = s.find('\n------------------------------------------------------------------------', start)
if sep < 0:
    raise SystemExit('expected separator after qTerminalProjectionUnique theorem not found')
replacement = '''qTerminalProjectionUnique_v147 t u refl refl refl =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (sym (QTerminalSolution_v147.stationarity u i)))
'''
s = s[:start] + replacement + s[sep:]
p.write_text(s)
print('terminal-uniqueness-normalization=structural')

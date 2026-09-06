from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('residualSquareNonzero_v140 :')
end = text.find('\n------------------------------------------------------------------------', start)
if start < 0 or end < 0:
    raise SystemExit('residual theorem block not found')
block = text[start:end]
block = block.replace('SmoothAlgebra.orderedRing S', 'SmoothAlgebra.orderedRing _')
text = text[:start] + block + text[end:]
path.write_text(text)
print('residual-proof-carrier-inferred=True')

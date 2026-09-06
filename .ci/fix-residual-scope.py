from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = '''residualSquareNonzero_v140 : ∀ {S}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
'''
new = '''residualSquareNonzero_v140 : ∀ {S}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))
'''
changed = old in text
if changed:
    text = text.replace(old, new, 1)
start = text.find('residualSquareNonzero_v140 :')
end = text.find('\n------------------------------------------------------------------------', start)
if start >= 0 and end >= 0:
    block = text[start:end]
    block2 = block.replace('SmoothAlgebra.orderedRing S', 'SmoothAlgebra.orderedRing _')
    if block2 != block:
        changed = True
        text = text[:start] + block2 + text[end:]
path.write_text(text)
print(f'residual-proof-carrier-signature-fixed={changed}')

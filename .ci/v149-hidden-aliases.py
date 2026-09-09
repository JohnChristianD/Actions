from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = '''record RecurrentAffine (S : SmoothAlgebra) (input hidden : Nat) : Set where
  field
    input : VecS S input
    hidden : VecS S hidden
'''
new = '''record RecurrentAffine (S : SmoothAlgebra) (inputDim hiddenDim : Nat) : Set where
  field
    inputState : VecS S inputDim
    hiddenState : VecS S hiddenDim
'''
if old in text:
    text = text.replace(old, new, 1)
# The transformed source may instead expose only the problematic field. Rename
# just that field in the RecurrentAffine block, preserving dimension variables.
start = text.find('record RecurrentAffine (S : SmoothAlgebra)')
if start < 0:
    raise SystemExit('RecurrentAffine declaration missing')
end = text.find('\n------------------------------------------------------------------------\n', start)
if end < 0:
    end = len(text)
block = text[start:end]
if '    hidden : VecS S hidden\n' in block:
    block = block.replace('    hidden : VecS S hidden\n', '    hiddenState : VecS S hidden\n', 1)
text = text[:start] + block + text[end:]
text = text.replace('RecurrentAffine.hidden ', 'RecurrentAffine.hiddenState ')
text = text.replace('RecurrentAffine.hidden\n', 'RecurrentAffine.hiddenState\n')
text = text.replace('RecurrentAffine.hidden)', 'RecurrentAffine.hiddenState)')
if '    hidden : VecS S hidden\n' in block:
    raise SystemExit('legacy RecurrentAffine hidden field remains')
path.write_text(text)
print('recurrent-affine-hidden-alias-normalized=True')

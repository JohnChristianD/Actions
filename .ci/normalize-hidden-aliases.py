from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = 'hidden : VecS S hidden'
new = 'hiddenVec : VecS S hidden'
count = text.count(old)
text = text.replace(old, new)
# Record projections corresponding to this field use .hidden. Limit to the
# same declaration family by updating the common projection spelling.
text = text.replace('.hidden ', '.hiddenVec ')
text = text.replace('.hidden\n', '.hiddenVec\n')
path.write_text(text)
print(f'hidden-alias-normalized={count > 0}; replacements={count}')

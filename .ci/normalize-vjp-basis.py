from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
pattern = r'(?m)^(\s*coeff \(var j\) _ i).*\n\s*\.\.\. \| yes _ = one\s*\n\s*\.\.\. \| no _ = zero\s*$'
replacement = r'\1 = basis j i'
text, count = re.subn(pattern, replacement, text, count=1)
if count == 0 and 'coeff (var j) _ i = basis j i' not in text:
    raise SystemExit('variable coeff equation not found')
path.write_text(text)
print(f'vjp-coeff-variable-as-basis-rewrite-count={count}; already-normalized={count == 0}')

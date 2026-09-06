from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
pattern = r'(?m)^(\s*)coeff \(var j\) _ i with finDecEq i j\n\1\.\.\. \| yes _ = one\n\1\.\.\. \| no _ = zero\s*$'
text, count = re.subn(pattern, r'\1coeff (var j) _ i = basis j i', text, count=1)
if count != 1:
    raise SystemExit(f'expected one variable coeff block, changed={count}')
path.write_text(text)
print('vjp-coeff-variable-as-basis=True')

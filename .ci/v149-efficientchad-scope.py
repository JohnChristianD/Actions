from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
start = s.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where\n')
if start < 0:
    raise SystemExit('EfficientCHAD module not found')
end = s.find('\n------------------------------------------------------------------------\n', start)
if end < 0:
    end = len(s)
block = s[start:end]
old_decl = '  R = Ring.R Rg\n'
new_decl = '  ScalarR = Ring.R Rg\n'
if old_decl in block:
    block = block.replace(old_decl, new_decl, 1)
elif new_decl not in block:
    raise SystemExit('EfficientCHAD scalar carrier declaration missing')
# Rename only the unqualified local alias. Preserve qualified Ring.R.
block = re.sub(r'(?<![A-Za-z0-9_.])R(?![A-Za-z0-9_])', 'ScalarR', block)
# The declaration above is already ScalarR and the negative lookaround leaves it untouched.
if '  ScalarR = Ring.R Rg\n' not in block:
    raise SystemExit('EfficientCHAD scalar carrier rename did not persist')
if re.search(r'(?m)^\s*R\s*=\s*Ring\.R\b', block):
    raise SystemExit('legacy EfficientCHAD local R alias remains')
s = s[:start] + block + s[end:]
p.write_text(s)
print('EfficientCHAD local carrier alias renamed from R to ScalarR')

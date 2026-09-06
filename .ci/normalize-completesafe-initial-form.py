from pathlib import Path
import re

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
pattern = r'(?m)^(\s*)initialForm\s*:\s*QRun_v142\.projection\s*\n\1\s+\(initialQRun_v142 D budget p x\)\s+≡\s+p\s*='
s2, count = re.subn(pattern, r'\1initialForm =', s, count=1)
if count > 1:
    raise SystemExit(f'unexpected duplicate initialForm binding: count={count}')
p.write_text(s2)
print(f'completesafe-initial-form-normalization=structural changed={count}')

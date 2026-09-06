from pathlib import Path
import re

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = text.find('\n------------------------------------------------------------------------', start + 10)
if start < 0 or end < 0:
    raise SystemExit('EfficientCHAD module region not found')
region = text[start:end]
patterns = [
    (r'(?<![_A-Za-z0-9.])c\s*\*\s*dexp\s*\(eval x ρ\)', 'Ring._*_ Rg c (SmoothAlgebra.dexp S (eval x ρ))'),
    (r'(?<![_A-Za-z0-9.])c\s*\*\s*dlog\s*\(eval x ρ\)', 'Ring._*_ Rg c (SmoothAlgebra.dlog S (eval x ρ))'),
    (r'(?<![_A-Za-z0-9.])c\s*\*\s*dtanh\s*\(eval x ρ\)', 'Ring._*_ Rg c (SmoothAlgebra.dtanh S (eval x ρ))'),
    (r'(?<![_A-Za-z0-9.])c\s*\*\s*dsigmoid\s*\(eval x ρ\)', 'Ring._*_ Rg c (SmoothAlgebra.dsigmoid S (eval x ρ))'),
]
changed = 0
for pat, repl in patterns:
    region, n = re.subn(pat, repl, region)
    changed += n
text = text[:start] + region + text[end:]
path.write_text(text)
print(f'vjp-unary-products-qualified={changed}')

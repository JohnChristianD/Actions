from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
repls = {
    'back px (c * dexp vx)': 'back px (Ring._*_ Rg c (SmoothAlgebra.dexp S vx))',
    'back px (c * dlog vx)': 'back px (Ring._*_ Rg c (SmoothAlgebra.dlog S vx))',
    'back px (c * dtanh vx)': 'back px (Ring._*_ Rg c (SmoothAlgebra.dtanh S vx))',
    'back px (c * dsigmoid vx)': 'back px (Ring._*_ Rg c (SmoothAlgebra.dsigmoid S vx))',
    'back px (c * dexp (eval x ρ))': 'back px (Ring._*_ Rg c (SmoothAlgebra.dexp S (eval x ρ)))',
    'back px (c * dlog (eval x ρ))': 'back px (Ring._*_ Rg c (SmoothAlgebra.dlog S (eval x ρ)))',
    'back px (c * dtanh (eval x ρ))': 'back px (Ring._*_ Rg c (SmoothAlgebra.dtanh S (eval x ρ)))',
    'back px (c * dsigmoid (eval x ρ))': 'back px (Ring._*_ Rg c (SmoothAlgebra.dsigmoid S (eval x ρ)))',
    '(c * dexp (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dexp S (eval x ρ)))',
    '(c * dlog (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dlog S (eval x ρ)))',
    '(c * dtanh (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dtanh S (eval x ρ)))',
    '(c * dsigmoid (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dsigmoid S (eval x ρ)))',
    'c * dexp (eval x ρ)': 'Ring._*_ Rg c (SmoothAlgebra.dexp S (eval x ρ))',
    'c * dlog (eval x ρ)': 'Ring._*_ Rg c (SmoothAlgebra.dlog S (eval x ρ))',
    'c * dtanh (eval x ρ)': 'Ring._*_ Rg c (SmoothAlgebra.dtanh S (eval x ρ))',
    'c * dsigmoid (eval x ρ)': 'Ring._*_ Rg c (SmoothAlgebra.dsigmoid S (eval x ρ))',
}
changed = 0
for old, new in repls.items():
    n = text.count(old)
    if n:
        text = text.replace(old, new)
        changed += n
path.write_text(text)
print(f'vjp-unary-products-qualified={changed}')

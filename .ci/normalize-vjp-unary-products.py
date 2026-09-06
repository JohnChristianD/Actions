from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = text.find('\n------------------------------------------------------------------------', start + 10)
if start < 0 or end < 0:
    raise SystemExit('EfficientCHAD module region not found')
region = text[start:end]
repls = {
    '(c * dexp (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dexp S (eval x ρ)))',
    '(c * dlog (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dlog S (eval x ρ)))',
    '(c * dtanh (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dtanh S (eval x ρ)))',
    '(c * dsigmoid (eval x ρ))': '(Ring._*_ Rg c (SmoothAlgebra.dsigmoid S (eval x ρ)))',
    '(dexp (eval x ρ))': '(SmoothAlgebra.dexp S (eval x ρ))',
    '(dlog (eval x ρ))': '(SmoothAlgebra.dlog S (eval x ρ))',
    '(dtanh (eval x ρ))': '(SmoothAlgebra.dtanh S (eval x ρ))',
    '(dsigmoid (eval x ρ))': '(SmoothAlgebra.dsigmoid S (eval x ρ))',
}
changed = 0
for old, new in repls.items():
    n = region.count(old)
    if n:
        region = region.replace(old, new)
        changed += n
text = text[:start] + region + text[end:]
path.write_text(text)
print(f'vjp-unary-products-qualified={changed}')

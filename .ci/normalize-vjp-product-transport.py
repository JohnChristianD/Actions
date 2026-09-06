from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start_marker = '  vjpCoeff (mul x y) ρ c i =\n'
end_marker = '  vjpCoeff (negE x) ρ c i =\n'
start = text.find(start_marker)
end = text.find(end_marker, start)
if start < 0 or end < 0:
    raise SystemExit('VJP product theorem block not found')
replacement = '''  vjpCoeff (mul x y) ρ c i =
    trans
      (cong₂ (Ring._+_ Rg)
        (trans
          (cong (λ d → Pullback.back (pull x ρ) d i)
            (cong (λ z → Ring._*_ Rg c z) (primalCorrect y ρ)))
          (vjpCoeff x ρ (Ring._*_ Rg c (eval y ρ)) i))
        (trans
          (cong (λ d → Pullback.back (pull y ρ) d i)
            (cong (λ z → Ring._*_ Rg c z) (primalCorrect x ρ)))
          (vjpCoeff y ρ (Ring._*_ Rg c (eval x ρ)) i)))
      (sym
        (Ring.distrib Rg c
          (Ring._*_ Rg (eval y ρ) (coeff x ρ i))
          (Ring._*_ Rg (eval x ρ) (coeff y ρ i))))
'''
text = text[:start] + replacement + text[end:]
path.write_text(text)
print('vjp-product-primal-transport=True')

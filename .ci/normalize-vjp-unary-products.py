from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start_marker = '  vjpCoeff (expE x) ρ c i =\n'
end_marker = '  data EState : Set where\n'
start = text.find(start_marker)
end = text.find(end_marker, start)
if start < 0 or end < 0:
    raise SystemExit('unary VJP theorem block not found')
replacement = '''  vjpCoeff (expE x) ρ c i =
    trans
      (vjpCoeff x ρ (Ring._*_ Rg c (SmoothAlgebra.dexp S (Pullback.value (pull x ρ)))) i)
      (trans
        (cong
          (λ d → Ring._*_ Rg d (coeff x ρ i))
          (cong
            (λ z → Ring._*_ Rg c (SmoothAlgebra.dexp S z))
            (primalCorrect x ρ)))
        (Ring.mulAssoc Rg c (SmoothAlgebra.dexp S (eval x ρ)) (coeff x ρ i)))
  vjpCoeff (logE x) ρ c i =
    trans
      (vjpCoeff x ρ (Ring._*_ Rg c (SmoothAlgebra.dlog S (Pullback.value (pull x ρ)))) i)
      (trans
        (cong
          (λ d → Ring._*_ Rg d (coeff x ρ i))
          (cong
            (λ z → Ring._*_ Rg c (SmoothAlgebra.dlog S z))
            (primalCorrect x ρ)))
        (Ring.mulAssoc Rg c (SmoothAlgebra.dlog S (eval x ρ)) (coeff x ρ i)))
  vjpCoeff (tanhE x) ρ c i =
    trans
      (vjpCoeff x ρ (Ring._*_ Rg c (SmoothAlgebra.dtanh S (Pullback.value (pull x ρ)))) i)
      (trans
        (cong
          (λ d → Ring._*_ Rg d (coeff x ρ i))
          (cong
            (λ z → Ring._*_ Rg c (SmoothAlgebra.dtanh S z))
            (primalCorrect x ρ)))
        (Ring.mulAssoc Rg c (SmoothAlgebra.dtanh S (eval x ρ)) (coeff x ρ i)))
  vjpCoeff (sigmoidE x) ρ c i =
    trans
      (vjpCoeff x ρ (Ring._*_ Rg c (SmoothAlgebra.dsigmoid S (Pullback.value (pull x ρ)))) i)
      (trans
        (cong
          (λ d → Ring._*_ Rg d (coeff x ρ i))
          (cong
            (λ z → Ring._*_ Rg c (SmoothAlgebra.dsigmoid S z))
            (primalCorrect x ρ)))
        (Ring.mulAssoc Rg c (SmoothAlgebra.dsigmoid S (eval x ρ)) (coeff x ρ i)))

'''
text = text[:start] + replacement + text[end:]
path.write_text(text)
print('vjp-unary-products-transported-from-pull-value=True')

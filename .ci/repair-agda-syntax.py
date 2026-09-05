from pathlib import Path

REWRITES = [
    (
        '  accumulate i c (state s) = state (λ j with finDecEq j i\n'
        '    ... | yes _ = s j + c\n'
        '    ... | no _ = s j)',
        '  accumulateAt : Fin n → R → Cot → Fin n → R\n'
        '  accumulateAt i c s j with finDecEq j i\n'
        '  ... | yes _ = s j + c\n'
        '  ... | no _ = s j\n\n'
        '  accumulate i c (state s) = state (λ j → accumulateAt i c s j)',
    ),
    (
        'let hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))\n'
        '        (mu * (hx * hx)) ≡ alpha =\n'
        '      trans',
        'let\n'
        '      hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))\n'
        '        (mu * (hx * hx)) ≡ alpha\n'
        '      hzero = trans',
    ),
    (
        'let OR = SmoothAlgebra.orderedRing _\n'
        '      Rg = OrderedRing.ring OR\n'
        '      hx : x ≠ zero = residualSquareNonzero_v140 ha hr\n'
        '      hxx : zero < x * x = OrderedRing.squarePositive hx\n'
        '      hlt : alpha < mu * (x * x) = OrderedRing.subLtZero hr\n'
        '      hmul = OrderedRing.mulLtPosLeft hlt hxx',
        'let\n'
        '      OR = SmoothAlgebra.orderedRing _\n'
        '      Rg = OrderedRing.ring OR\n'
        '      hx : x ≠ zero\n'
        '      hx = residualSquareNonzero_v140 ha hr\n'
        '      hxx : zero < x * x\n'
        '      hxx = OrderedRing.squarePositive hx\n'
        '      hlt : alpha < mu * (x * x)\n'
        '      hlt = OrderedRing.subLtZero hr\n'
        '      hmul = OrderedRing.mulLtPosLeft hlt hxx',
    ),
    (
        'let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)\n'
        '      c = d * e\n'
        '      hc = OrderedRing.mulPos hd he\n'
        '      leftNorm : c * (a * SmoothAlgebra.recip _ d) ≡ a * e =\n',
        'let\n'
        '      Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)\n'
        '      c = d * e\n'
        '      hc = OrderedRing.mulPos hd he\n'
        '      leftNorm : c * (a * SmoothAlgebra.recip _ d) ≡ a * e\n'
        '      leftNorm =\n',
    ),
    (
        '      rightNorm : c * (b * SmoothAlgebra.recip _ e) ≡ b * d =\n',
        '      rightNorm : c * (b * SmoothAlgebra.recip _ e) ≡ b * d\n'
        '      rightNorm =\n',
    ),
    (
        'let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)\n'
        '      e = diagonalNewtonExposure_v146 h\n'
        '      he = diagonalNewtonExposurePositive_v146 h\n'
        '      hb = projectionBudget_v146 h\n'
        '      hdef : hb ≡ CoupledHyperParameters_v146.q h * e = refl\n'
        '      hcancel : e * SmoothAlgebra.recip _ e ≡ one =\n'
        '        SmoothAlgebra.reciprocalLaw _ he\n',
        'let\n'
        '      Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)\n'
        '      e = diagonalNewtonExposure_v146 h\n'
        '      he = diagonalNewtonExposurePositive_v146 h\n'
        '      hb = projectionBudget_v146 h\n'
        '      hdef : hb ≡ CoupledHyperParameters_v146.q h * e\n'
        '      hdef = refl\n'
        '      hcancel : e * SmoothAlgebra.recip _ e ≡ one\n'
        '      hcancel = SmoothAlgebra.reciprocalLaw _ he\n',
    ),
    (
        '        hzero : d * zero ≡ zero = OrderedRing.mulZeroR Rg d\n'
        '        hone : zero < one = OrderedRing.zeroLtOne {orderedRing = OR}\n',
        '        hzero : d * zero ≡ zero\n'
        '        hzero = OrderedRing.mulZeroR Rg d\n'
        '        hone : zero < one\n'
        '        hone = OrderedRing.zeroLtOne {orderedRing = OR}\n',
    ),
]

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text
    for old, replacement in REWRITES:
        new = new.replace(old, replacement, 1)
    if new != text:
        path.write_text(new)
        changed += 1
print(f'grammar-repaired-files={changed}')

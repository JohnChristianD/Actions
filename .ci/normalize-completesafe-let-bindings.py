from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
replacements = {
    '      hx : x ≠ zero =': '      hx =',
    '      hxx : zero < x * x =': '      hxx =',
    '      hlt : alpha < mu * (x * x) =': '      hlt =',
    '      leftNorm : c * (a * SmoothAlgebra.recip _ d) ≡ a * e =': '      leftNorm =',
    '      rightNorm : c * (b * SmoothAlgebra.recip _ e) ≡ b * d =': '      rightNorm =',
    '        hzero : d * zero ≡ zero =': '        hzero =',
    '      hdef : hb ≡ CoupledHyperParameters_v146.q h * e =': '      hdef =',
}
changed = 0
for old, new in replacements.items():
    count = s.count(old)
    if count > 1:
        raise SystemExit(f'unexpected duplicate typed-let binding: {old!r} count={count}')
    if count == 1:
        s = s.replace(old, new)
        changed += 1
p.write_text(s)
print(f'completesafe-let-normalization=typed-let-bindings-to-inferred-bindings changed={changed}')

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
counts = {}
for old, new in replacements.items():
    count = s.count(old)
    counts[old] = count
    s = s.replace(old, new)
if any(v != 1 for v in counts.values()):
    raise SystemExit('unexpected typed-let binding counts: ' + repr(counts))
p.write_text(s)
print('completesafe-let-normalization=typed-let-bindings-to-inferred-bindings')

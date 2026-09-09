from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

marker_start = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
marker_end = "------------------------------------------------------------------------\n-- Seven coupled parameter blocks and finite parameter indices\n"
if s.count(marker_start) != 1 or s.count(marker_end) != 1:
    raise SystemExit(f'unexpected monolith markers: start={s.count(marker_start)} end={s.count(marker_end)}')

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
replacement = needle + "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n"
if s.count(needle) != 1:
    raise SystemExit(f'unexpected reciprocal law count: {s.count(needle)}')
s = s.replace(needle, replacement, 1)

start = s.index(marker_start)
end = s.index(marker_end, start)
s = s[:start] + s[start:end].replace(s[start:end].split(marker_start,1)[1].split('\n',1)[0] if False else '', '') + s[end:]
# The canonical marker block above is already unique on branch; duplicate marker
# removal is intentionally structural and only applies when a second block is present.
if s.count(marker_start) > 1:
    first = s.index(marker_start)
    second = s.index(marker_start, first + 1)
    second_end = s.index(marker_end, second)
    s = s[:second] + s[second_end:]

old_acc = """  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)
"""
new_acc = """  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)
"""
if s.count(old_acc) == 1:
    s = s.replace(old_acc, new_acc, 1)

# residualSquareNonzero_v140
rstart = s.find('residualSquareNonzero_v140 ')
if rstart < 0: raise SystemExit('residual theorem marker not found')
rsep = s.find('\n------------------------------------------------------------------------', rstart)
residual = '''residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
  λ hx →
    let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
        hxx0 = trans
          (cong₂ (Ring._*_ Rg) hx hx)
          (Ring.zeroMulL Rg zero)
        hmu0 = trans
          (cong (λ q → mu * q) hxx0)
          (Ring.zeroMulR Rg mu)
        hneg0 = trans
          (cong (λ q → Ring.neg Rg q) hmu0)
          (trans
            (sym (Ring.addZeroR Rg (Ring.neg Rg zero)))
            (Ring.addNegL Rg zero))
        hzero = trans
          (cong (λ q → alpha + q) hneg0)
          (Ring.addZeroR Rg alpha)
        hlt = subst (λ q → q < zero) hzero hr
    in OrderedRing.notLtFromLe ha hlt
'''
s = s[:rstart] + residual + s[rsep:]

# qProjectionCross_v141
qstart = s.find('qProjectionCross_v141 ')
if qstart < 0: raise SystemExit('q projection theorem marker not found')
qsep = s.find('\n------------------------------------------------------------------------', qstart)
qcross = '''qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hx = residualSquareNonzero_v140 ha hr
      hxx = OrderedRing.squarePositive hx
      hlt = OrderedRing.subLtZero hr
      hmul = OrderedRing.mulLtPosLeft hlt hxx
      hright =
        trans
          (Ring.mulComm Rg (x * x) (mu * (x * x)))
          (sym (Ring.mulAssoc Rg mu (x * x) (x * x)))
  in trans
       (trans
         (sym (Ring.mulComm Rg alpha (x * x)))
         hmul)
       hright
'''
s = s[:qstart] + qcross + s[qsep:]

# orderedFieldCrossStrict_v142
cstart = s.find('orderedFieldCrossStrict_v142 ')
if cstart < 0: raise SystemExit('cross theorem marker not found')
csep = s.find('\n------------------------------------------------------------------------', cstart)
cross = '''orderedFieldCrossStrict_v142 a b d e hd he h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      c = d * e
      rd = SmoothAlgebra.recip _ d
      re = SmoothAlgebra.recip _ e
      hleft =
        trans
          (Ring.mulComm Rg c (a * rd))
          (trans
            (Ring.mulAssoc Rg a rd c)
            (trans
              (cong (λ q → a * q)
                (trans
                  (sym (Ring.mulAssoc Rg rd d e))
                  (trans
                    (cong (λ q → q * e) (Ring.mulComm Rg rd d))
                    (trans
                      (cong (λ q → q * e) (SmoothAlgebra.reciprocalLaw _ hd))
                      (Ring.mulOneL Rg e)))))
              (Ring.mulOneR Rg a)))
      hright =
        trans
          (Ring.mulComm Rg c (b * re))
          (trans
            (Ring.mulAssoc Rg b re c)
            (trans
              (cong (λ q → b * q)
                (trans
                  (sym (Ring.mulAssoc Rg re e d))
                  (trans
                    (cong (λ q → q * d) (Ring.mulComm Rg re e))
                    (trans
                      (cong (λ q → q * d) (SmoothAlgebra.reciprocalLaw _ he))
                      (Ring.mulOneL Rg d)))))
              (Ring.mulOneR Rg b)))
      hcross = transportLt_v142 hleft hright h
  in OrderedRing.mulLtPosCancelLeft hcross (OrderedRing.mulPos hd he)
'''
s = s[:cstart] + cross + s[csep:]

# multiplierDeletionStrict_v142
mstart = s.find('multiplierDeletionStrict_v142 ')
if mstart < 0: raise SystemExit('multiplier theorem marker not found')
msep = s.find('\n------------------------------------------------------------------------', mstart)
mult = '''multiplierDeletionStrict_v142 n d y z hd he h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hnz = OrderedRing.negLt h
      base = n * d
      negMul =
        trans
          (sym (Ring.negScale Rg d y))
          (cong (Ring.neg Rg) (Ring.mulComm Rg d y))
      lhs =
        trans
          (Ring.distrib Rg n d (neg z))
          (cong₂ _+_ refl (sym (Ring.negScale Rg n z)))
      rhs =
        trans
          (Ring.distrib Rg d n (neg y))
          (cong₂ _+_ (Ring.mulComm Rg d n) negMul)
      cross = OrderedRing.addLtLeft hnz base
      cross' = transportLt_v142 lhs rhs cross
  in orderedFieldCrossStrict_v142 n (n + neg y) d (d + neg z) hd he cross'
'''
s = s[:mstart] + mult + s[msep:]

# reciprocalNonnegative_v146
rn = s.find('reciprocalNonnegative_v146 {S} {d} hd with')
if rn < 0: raise SystemExit('reciprocal nonnegative theorem marker not found')
rnsep = s.find('\n------------------------------------------------------------------------', rn)
recip = '''reciprocalNonnegative_v146 {S} {d} hd with
  ltDec (SmoothAlgebra.orderedRing S)
    (SmoothAlgebra.recip S d) zero
... | yes hneg =
  ⊥-elim
    (OrderedRing.notLtFromLe
      (OrderedRing.ltLe (OrderedRing.zeroLtOne
        {orderedRing = SmoothAlgebra.orderedRing S}))
      (trans
        (sym (SmoothAlgebra.reciprocalLaw S hd))
        (trans
          (OrderedRing.mulLtPosLeft hneg hd)
          (Ring.mulZeroR
            (OrderedRing.ring (SmoothAlgebra.orderedRing S)) d))))
... | no h = h
'''
s = s[:rn] + recip + s[rnsep:]

# Delete the malformed audited-KKT placeholder. The constructive theorem
# remains later in the monolith; this removes only documentation accidentally
# emitted as executable declarations.
kmarker = '-- The theorem to be exported after kernel checking is:'
kstart = s.find(kmarker)
if kstart >= 0:
    ksep = s.find('\n------------------------------------------------------------------------', kstart)
    if ksep < 0: raise SystemExit('audited KKT placeholder separator not found')
    placeholder = '''-- The old audited KKT placeholder was documentation, not a theorem.
-- The executable constructive KKT theorem is defined below.
'''
    s = s[:kstart] + placeholder + s[ksep:]

# Terminal uniqueness
old_terminal = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
if s.count(old_terminal) != 1: raise SystemExit('terminal uniqueness theorem count mismatch')
tstart = s.index(old_terminal)
tsep = s.find('\n------------------------------------------------------------------------', tstart)
terminal = '''qTerminalProjectionUnique_v147 t u refl refl refl =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (sym (QTerminalSolution_v147.stationarity u i)))
'''
s = s[:tstart] + terminal + s[tsep:]

checks = [
    'record SmoothAlgebra : Set₁ where',
    'sqrtDomain : R → Set',
    'sqrtSquareLaw :',
    'accumulateAt : Fin n → R → Cot → Fin n → R',
    'residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =',
    'qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =',
    'orderedFieldCrossStrict_v142 a b d e hd he h =',
    'multiplierDeletionStrict_v142 n d y z hd he h =',
    'reciprocalNonnegative_v146 {S} {d} hd with',
    'qTerminalProjectionUnique_v147 t u refl refl refl =']
for needle in checks:
    if s.count(needle) != 1: raise SystemExit(f'missing/duplicate target: {needle}')

if s.count(kmarker) != 0:
    raise SystemExit('malformed audited KKT placeholder marker survived')

p.write_text(s)
print('monolith canonical algebra/parser/residual/q-cross/reciprocal-cross/multiplier/reciprocal-nonnegative/audited-KKT/terminal normalization applied exactly once')

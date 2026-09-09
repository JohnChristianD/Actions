from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

marker_start = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
marker_end = "------------------------------------------------------------------------\n-- Seven coupled parameter blocks and finite parameter indices\n"
if marker_start not in s or marker_end not in s:
    raise SystemExit('canonical SmoothAlgebra markers not found')

first = s.index(marker_start)
search = s.find(marker_start, first + len(marker_start))
while search >= 0:
    close = s.find(marker_end, search + len(marker_start))
    if close < 0:
        raise SystemExit('duplicate SmoothAlgebra marker has no closing marker')
    s = s[:search] + s[close:]
    search = s.find(marker_start, search)

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
if needle in s and '    sqrtDomain : R → Set\n' not in s:
    s = s.replace(needle, needle + "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n", 1)

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
if old_acc in s:
    s = s.replace(old_acc, new_acc, 1)

# residualSquareNonzero_v140
rstart = s.find('residualSquareNonzero_v140 ')
if rstart < 0: raise SystemExit('residual theorem marker not found')
rsep = s.find('\n------------------------------------------------------------------------', rstart)
s = s[:rstart] + '''residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
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
''' + s[rsep:]

# qProjectionCross_v141
qstart = s.find('qProjectionCross_v141 ')
if qstart < 0: raise SystemExit('q projection theorem marker not found')
qsep = s.find('\n------------------------------------------------------------------------', qstart)
s = s[:qstart] + '''qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
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
''' + s[qsep:]

# orderedFieldCrossStrict_v142
cstart = s.find('orderedFieldCrossStrict_v142 ')
if cstart < 0: raise SystemExit('cross theorem marker not found')
csep = s.find('\n------------------------------------------------------------------------', cstart)
s = s[:cstart] + '''orderedFieldCrossStrict_v142 a b d e hd he h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      rd = SmoothAlgebra.recip _ d
      re = SmoothAlgebra.recip _ e
      hleft =
        trans
          (Ring.mulComm Rg (d * e) (a * rd))
          (trans
            (Ring.mulAssoc Rg a rd (d * e))
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
          (Ring.mulComm Rg (d * e) (b * re))
          (trans
            (Ring.mulAssoc Rg b re (d * e))
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
''' + s[csep:]

# multiplierDeletionStrict_v142
mstart = s.find('multiplierDeletionStrict_v142 ')
if mstart < 0: raise SystemExit('multiplier theorem marker not found')
msep = s.find('\n------------------------------------------------------------------------', mstart)
s = s[:mstart] + '''multiplierDeletionStrict_v142 n d y z hd he h =
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
''' + s[msep:]

# reciprocalNonnegative_v146
rn = s.find('reciprocalNonnegative_v146 {S} {d} hd with')
if rn < 0: raise SystemExit('reciprocal nonnegative theorem marker not found')
rnsep = s.find('\n------------------------------------------------------------------------', rn)
s = s[:rn] + '''reciprocalNonnegative_v146 {S} {d} hd with
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
''' + s[rnsep:]

# qProjectionRetraction_v147 initial-form identity
iform = '      initialForm : QRun_v142.projection'
start = s.find(iform)
if start >= 0:
    sep = s.find('\n  in trans stopped initialForm', start)
    if sep < 0: raise SystemExit('qProjectionRetraction initialForm terminator not found')
    s = s[:start] + '''      initialForm =
        trans
          (cong (λ mu → qCandidate_v142 D mu
            (allActive_v147 {n = _}) p x) muZero)
          (qCandidateZero_v147 D p x)
''' + s[sep:]

# Remove malformed audited-KKT documentation placeholder.
kmarker = '-- The theorem to be exported after kernel checking is:'
kstart = s.find(kmarker)
if kstart >= 0:
    ksep = s.find('\n------------------------------------------------------------------------', kstart)
    if ksep < 0: raise SystemExit('audited KKT placeholder separator not found')
    s = s[:kstart] + '''-- The old audited KKT placeholder was documentation, not a theorem.
-- The executable constructive KKT theorem is defined below.
''' + s[ksep:]

# qTerminalProjectionUnique_v147
old_terminal = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
if s.count(old_terminal) != 1: raise SystemExit('terminal uniqueness theorem count mismatch')
tstart = s.index(old_terminal)
tsep = s.find('\n------------------------------------------------------------------------', tstart)
s = s[:tstart] + '''qTerminalProjectionUnique_v147 t u refl refl refl =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (sym (QTerminalSolution_v147.stationarity u i)))
''' + s[tsep:]

if s.count(marker_start) != 1: raise SystemExit('canonical marker count is not one')
if s.count('sqrtDomain : R → Set') != 1: raise SystemExit('sqrt domain law missing or duplicated')
if s.count(kmarker) != 0: raise SystemExit('malformed audited KKT placeholder marker survived')

p.write_text(s)
print('cumulative v149 monolith normalization applied deterministically')

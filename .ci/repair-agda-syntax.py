from pathlib import Path
import re

replacements = [
("""  accumulate i c (state s) = state (λ j with finDecEq j i)
    ... | yes _ = s j + c
    ... | no _ = s j)""", """  accumulate i c (state s) = state (λ j → addAt j)
    where
    addAt : Fin n → R
    addAt j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j"""),
("""insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }""", """insertCVT_v142 D a i f = record { cell = choose i }
  where
  choose : Fin cells → CVTSlot_v142 S
  choose j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }"""),
("""residualSquareNonzero_v140 ha hr hx =
  let hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))
        (mu * (hx * hx)) ≡ alpha =
      trans
        (cong (λ q → alpha + Ring.neg (OrderedRing.ring _) (mu * q))
          (cong₂ (Ring._*_ (OrderedRing.ring _)) hx hx))
        (Ring.addZeroR (OrderedRing.ring _) alpha)
  in ⊥-elim (OrderedRing.notLtFromLe ha (subst (λ q → zero ≤ q) hzero hr))""", """residualSquareNonzero_v140 ha hr hx = λ x0 →
  OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing S) ha
    (subst (λ q → q < Ring.zero Rg) hzero hr)
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  hzero : alpha + Ring.neg Rg (Ring._*_ Rg mu (Ring._*_ Rg x x)) ≡ alpha
  hzero = trans
    (cong (λ q → alpha + Ring.neg Rg (Ring._*_ Rg mu q))
      (cong₂ (Ring._*_ Rg) x0 x0))
    (Ring.addZeroR Rg alpha)"""),
("""qProjectionCross_v141 ha hr =
  let OR = SmoothAlgebra.orderedRing _
      Rg = OrderedRing.ring OR
      hx : x ≠ zero = residualSquareNonzero_v140 ha hr
      hxx : zero < x * x = OrderedRing.squarePositive hx
      hlt : alpha < mu * (x * x) = OrderedRing.subLtZero hr
      hmul = OrderedRing.mulLtPosLeft hlt hxx
  in trans
       (trans
         (sym (Ring.mulComm Rg alpha (x * x)))
         hmul)
       (trans
         (Ring.mulComm Rg (x * x) (mu * (x * x)))
         (sym (Ring.mulAssoc Rg mu (x * x) (x * x))))""", """qProjectionCross_v141 ha hr =
  trans
    (trans
      (sym (Ring.mulComm Rg alpha (Ring._*_ Rg x x)))
      hmul)
    (trans
      (Ring.mulComm Rg (Ring._*_ Rg x x)
        (Ring._*_ Rg mu (Ring._*_ Rg x x)))
      (sym (Ring.mulAssoc Rg mu (Ring._*_ Rg x x) (Ring._*_ Rg x x))))
  where
  OR = SmoothAlgebra.orderedRing S
  Rg = OrderedRing.ring OR
  hx = residualSquareNonzero_v140 ha hr
  hxx = OrderedRing.squarePositive OR hx
  hlt = OrderedRing.subLtZero OR hr
  hmul = OrderedRing.mulLtPosLeft hlt hxx""")]

for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text
    for old, fixed in replacements:
        new = new.replace(old, fixed, 1)
    if new != text:
        path.write_text(new)

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts:
        for line_no, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r'λ[^\n]*\bwith\b', line):
                remaining.append(f'{path}:{line_no}:{line}')
if remaining:
    print('\n'.join(remaining))
    raise SystemExit(1)

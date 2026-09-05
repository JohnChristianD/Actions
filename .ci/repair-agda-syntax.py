from pathlib import Path
import re

def replace_equation(text: str, name: str, fixed: str) -> str:
    marker = name + " "
    start = text.find(marker)
    if start < 0:
        return text
    eq = text.find("=", start)
    if eq < 0:
        return text
    sep = text.find("------------------------------------------------------------------------", eq)
    if sep < 0:
        return text
    return text[:start] + fixed.rstrip() + "\n" + text[sep:]

ACCUMULATE_OLD = """  accumulate i c (state s) = state (λ j with finDecEq j i)
    ... | yes _ = s j + c
    ... | no _ = s j)"""
ACCUMULATE_FIXED = """  accumulate i c (state s) = state (λ j → addAt j)
    where
    addAt : Fin n → R
    addAt j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j"""

INSERT_FIXED = """insertCVT_v142 D a i f = record { cell = choose i }
  where
  choose : Fin cells → CVTSlot_v142 S
  choose j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }"""

RESIDUAL_FIXED = """residualSquareNonzero_v140 ha hr hx = λ x0 →
  OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing S) ha
    (subst (λ q → q < Ring.zero Rg) hzero hr)
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

  hzero : alpha + Ring.neg Rg (Ring._*_ Rg mu (Ring._*_ Rg x x)) ≡ alpha
  hzero = trans
    (cong (λ q → alpha + Ring.neg Rg (Ring._*_ Rg mu q))
      (cong₂ (Ring._*_ Rg) x0 x0))
    (Ring.addZeroR Rg alpha)"""

CROSS_FIXED = """qProjectionCross_v141 ha hr =
  trans
    (trans
      (sym (Ring.mulComm Rg alpha (Ring._*_ Rg x x)))
      hmul)
    (trans
      (Ring.mulComm Rg (Ring._*_ Rg x x)
        (Ring._*_ Rg mu (Ring._*_ Rg x x)))
      (sym (Ring.mulAssoc Rg mu (Ring._*_ Rg x x) (Ring._*_ Rg x x))))
  where
  OR : OrderedRing
  OR = SmoothAlgebra.orderedRing S
  Rg : Ring
  Rg = OrderedRing.ring OR
  hx : x ≠ Ring.zero Rg
  hx = residualSquareNonzero_v140 ha hr
  hxx : Ring.zero Rg < Ring._*_ Rg x x
  hxx = OrderedRing.squarePositive OR hx
  hlt : x * x < Ring._*_ Rg mu (Ring._*_ Rg x x)
  hlt = OrderedRing.subLtZero OR hr
  hmul : (Ring._*_ Rg x x) * alpha <
    (Ring._*_ Rg x x) * (mu * (x * x))
  hmul = OrderedRing.mulLtPosLeft hlt hxx"""

ORDERED_FIXED = """orderedFieldCrossStrict_v142 a b d e hd he h =
  OrderedRing.mulLtPosCancelLeft (transportLt_v142 leftNorm rightNorm h) hc
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  c : Scalar S
  c = d * e
  hc : zero < c
  hc = OrderedRing.mulPos hd he
  leftNorm : c * (a * SmoothAlgebra.recip _ d) ≡ a * e
  leftNorm = trans (Ring.mulComm Rg c (a * SmoothAlgebra.recip _ d))
    (trans (Ring.mulAssoc Rg a (SmoothAlgebra.recip _ d) c)
      (trans (cong (λ q → a * q)
        (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ d) d e))
          (trans (cong (λ q → q * e) (Ring.mulComm Rg (SmoothAlgebra.recip _ d) d))
            (trans (cong (λ q → q * e) (SmoothAlgebra.reciprocalLaw _ hd))
              (Ring.mulOneL Rg e))))) refl))
  rightNorm : c * (b * SmoothAlgebra.recip _ e) ≡ b * d
  rightNorm = trans (Ring.mulComm Rg c (b * SmoothAlgebra.recip _ e))
    (trans (Ring.mulAssoc Rg b (SmoothAlgebra.recip _ e) c)
      (trans (cong (λ q → b * q)
        (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ e) e d))
          (trans (cong (λ q → q * d) (Ring.mulComm Rg (SmoothAlgebra.recip _ e) e))
            (trans (cong (λ q → q * d) (SmoothAlgebra.reciprocalLaw _ he))
              (Ring.mulOneL Rg d))))) refl))"""

MULT_FIXED = """multiplierDeletionStrict_v142 n d y z hd he h =
  orderedFieldCrossStrict_v142 n (n + neg y) d (d + neg z) hd he cross'
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  base : Scalar S
  base = n * d
  lhs : n * (d + neg z) ≡ base + neg (n * z)
  lhs = trans (Ring.distrib Rg n d (neg z))
    (cong₂ _+_ refl (sym (Ring.negScale Rg n z)))
  rhs : (n + neg y) * d ≡ base + neg (y * d)
  rhs = trans (Ring.distrib Rg d n (neg y))
    (trans (cong₂ _+_ (Ring.mulComm Rg d n) refl)
      (cong₂ _+_ refl
        (trans (Ring.mulComm Rg (neg y) d)
          (sym (Ring.negScale Rg y d)))))
  cross : base + neg (n * z) < base + neg (y * d)
  cross = OrderedRing.addLtLeft (OrderedRing.negLt h) base
  cross' : n * (d + neg z) < (n + neg y) * d
  cross' = transportLt_v142 lhs rhs cross"""

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text.replace(ACCUMULATE_OLD, ACCUMULATE_FIXED, 1)
    new = replace_equation(new, "insertCVT_v142", INSERT_FIXED)
    new = replace_equation(new, "residualSquareNonzero_v140", RESIDUAL_FIXED)
    new = replace_equation(new, "qProjectionCross_v141", CROSS_FIXED)
    new = replace_equation(new, "orderedFieldCrossStrict_v142", ORDERED_FIXED)
    new = replace_equation(new, "multiplierDeletionStrict_v142", MULT_FIXED)
    if new != text:
        path.write_text(new)
        changed += 1

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts:
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r'λ[^\n]*\bwith\b', line):
                remaining.append(f'{path}:{lineno}:{line}')

if remaining:
    print('\n'.join(remaining))
    raise SystemExit('unrepaired extended lambda syntax remains')

print(f'repaired-agda-files={changed}')

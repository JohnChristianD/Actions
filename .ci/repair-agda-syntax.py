from pathlib import Path
import re

ACC_PREFIX = '  accumulate i c (state s) = state (λ j with finDecEq j i'
ACC_FIXED = '''  accumulate i c (state s) = state (λ j → addAt j)
    where
    addAt : Fin n → R
    addAt j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j'''

CVT_FIXED = '''insertCVT_v142 D a i f = record { cell = choose i }
  where
  choose : Fin cells → CVTSlot_v142 S
  choose j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }'''

RESIDUAL_FIXED = '''residualSquareNonzero_v140 ha hr hx = λ x0 →
  OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing S) ha
    (subst (λ q → q < Ring.zero Rg) hzero hr0)
  where
  Rg : Ring
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)

  hr0 : alpha + Ring.neg Rg (mu * (x * x)) < Ring.zero Rg
  hr0 = subst
    (λ q → alpha + Ring.neg Rg (mu * q) < Ring.zero Rg)
    x0 hr

  hxx : Ring._*_ Rg x x ≡ Ring.zero Rg
  hxx = trans
    (cong₂ (Ring._*_ Rg) x0 x0)
    (Ring.mulZeroR Rg (Ring.zero Rg))

  hmux : Ring._*_ Rg mu (Ring._*_ Rg x x) ≡ Ring.zero Rg
  hmux = trans
    (cong (Ring._*_ Rg mu) hxx)
    (Ring.mulZeroR Rg mu)

  hnegzero : Ring.neg Rg (Ring.zero Rg) ≡ Ring.zero Rg
  hnegzero = trans
    (sym (Ring.addZeroR Rg (Ring.neg Rg (Ring.zero Rg))))
    (Ring.addNegL Rg (Ring.zero Rg))

  hzero : alpha + Ring.neg Rg (mu * (x * x)) ≡ alpha
  hzero = trans
    (cong (λ q → alpha + Ring.neg Rg q) hmux)
    (trans
      (cong (λ q → alpha + q) hnegzero)
      (Ring.addZeroR Rg alpha))'''

ORDERED_MARK = 'orderedFieldCrossStrict_v142 a b d e hd he h ='
ORDERED_FIXED = '''orderedFieldCrossStrict_v142 a b d e hd he h =
  OrderedRing.mulLtPosCancelLeft (transportLt_v142 leftNorm rightNorm h) hc
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  c = d * e
  hc = OrderedRing.mulPos hd he
  leftNorm = trans (Ring.mulComm Rg c (a * SmoothAlgebra.recip _ d))
    (trans (Ring.mulAssoc Rg a (SmoothAlgebra.recip _ d) c)
      (trans (cong (λ q → a * q)
        (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ d) d e))
          (trans (cong (λ q → q * e) (Ring.mulComm Rg (SmoothAlgebra.recip _ d) d))
            (trans (cong (λ q → q * e) (SmoothAlgebra.reciprocalLaw _ hd))
              (Ring.mulOneL Rg e))))) refl))
  rightNorm = trans (Ring.mulComm Rg c (b * SmoothAlgebra.recip _ e))
    (trans (Ring.mulAssoc Rg b (SmoothAlgebra.recip _ e) c)
      (trans (cong (λ q → b * q)
        (trans (sym (Ring.mulAssoc Rg (SmoothAlgebra.recip _ e) e d))
          (trans (cong (λ q → q * d) (Ring.mulComm Rg (SmoothAlgebra.recip _ e) e))
            (trans (cong (λ q → q * d) (SmoothAlgebra.reciprocalLaw _ he))
              (Ring.mulOneL Rg d))))) refl))'''

MULT_MARK = 'multiplierDeletionStrict_v142 n d y z hd he h ='
MULT_FIXED = '''multiplierDeletionStrict_v142 n d y z hd he h =
  orderedFieldCrossStrict_v142 n (n + neg y) d (d + neg z) hd he cross'
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  base = n * d
  lhs = trans (Ring.distrib Rg n d (neg z))
    (cong₂ _+_ refl (sym (Ring.negScale Rg n z)))
  rhs = trans (Ring.distrib Rg d n (neg y))
    (trans (cong₂ _+_ (Ring.mulComm Rg d n) refl)
      (cong₂ _+_ refl
        (trans (Ring.mulComm Rg (neg y) d)
          (sym (Ring.negScale Rg y d)))))
  cross = OrderedRing.addLtLeft (OrderedRing.negLt h) base
  cross' = transportLt_v142 lhs rhs cross'''


def replace_function(text: str, marker: str, replacement: str) -> str:
    start = text.find(marker)
    if start < 0:
        return text
    sep = text.find('\n------------------------------------------------------------------------\n', start)
    if sep < 0:
        return text
    line_start = text.rfind('\n', 0, start) + 1
    return text[:line_start] + replacement.rstrip() + text[sep:]

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    lines = text.splitlines()
    out = []
    i = 0
    structural = False
    while i < len(lines):
        if ACC_PREFIX in lines[i]:
            indent = lines[i].split('accumulate', 1)[0]
            out.extend([indent + s for s in ACC_FIXED.splitlines()])
            structural = True
            i += 3
            continue
        out.append(lines[i])
        i += 1
    new = '\n'.join(out) + ('\n' if text.endswith('\n') else '')
    new = replace_function(new, 'insertCVT_v142 D a i f =', CVT_FIXED)
    new = replace_function(new, 'residualSquareNonzero_v140 ha hr hx =', RESIDUAL_FIXED)
    new = replace_function(new, ORDERED_MARK, ORDERED_FIXED)
    new = replace_function(new, MULT_MARK, MULT_FIXED)
    if new != text:
        path.write_text(new)
        changed += 1

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if re.search(r'λ[^\n]*\bwith\b', line):
            remaining.append(f'{path}:{line_no}:{line}')
if remaining:
    print('\n'.join(remaining))
    raise SystemExit(1)
print(f'repaired-agda-files={changed}')

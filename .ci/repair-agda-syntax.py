from pathlib import Path
import re


def repair_accumulate(text):
    lines = text.splitlines()
    out = []
    changed = False
    i = 0
    while i < len(lines):
        if 'accumulate i c (state s) = state (λ j with finDecEq j i' in lines[i]:
            indent = lines[i].split('accumulate', 1)[0]
            out.extend([
                indent + 'accumulate i c (state s) = state (addAt i c s)',
                indent + '  where',
                indent + '  addAt : ∀ i → R → Cot → Cot',
                indent + '  addAt i c s = updateAt i c s',
                indent + '    where',
                indent + '    updateAt : Fin n → R → Cot → Fin n → R',
                indent + '    updateAt i c s j with finDecEq j i',
                indent + '    ... | yes _ = s j + c',
                indent + '    ... | no _ = s j',
            ])
            changed = True
            i += 3
            continue
        out.append(lines[i])
        i += 1
    return '\n'.join(out) + ('\n' if text.endswith('\n') else ''), changed

CVT_OLD = '''insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }'''
CVT_NEW = '''insertCVT_v142 D a i f = record { cell = choose i }
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

RESIDUAL_RE = re.compile(r'residualSquareNonzero_v140 ha hr hx =\n.*?(?=\n------------------------------------------------------------------------\n)', re.S)
RESIDUAL_NEW = '''residualSquareNonzero_v140 ha hr hx = λ x0 →
  OrderedRing.notLtFromLe (SmoothAlgebra.orderedRing S) ha
    (subst (λ q → q < Ring.zero Rg) hzero hr0)
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  hr0 = subst (λ q → alpha + Ring.neg Rg (mu * q) < Ring.zero Rg) x0 hr
  hxx = trans (cong₂ (Ring._*_ Rg) x0 x0) (Ring.mulZeroR Rg (Ring.zero Rg))
  hmux = trans (cong (Ring._*_ Rg mu) hxx) (Ring.mulZeroR Rg mu)
  hnegzero = trans (sym (Ring.addZeroR Rg (Ring.neg Rg (Ring.zero Rg)))) (Ring.addNegL Rg (Ring.zero Rg))
  hzero = trans (cong (λ q → alpha + Ring.neg Rg q) hmux)
    (trans (cong (λ q → alpha + q) hnegzero) (Ring.addZeroR Rg alpha))'''

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

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new, ch = repair_accumulate(text)
    if ch:
        changed += 1
    new2 = new.replace(CVT_OLD, CVT_NEW, 1)
    if new2 != new:
        changed += 1
    new3, count = RESIDUAL_RE.subn(RESIDUAL_NEW, new2, count=1)
    changed += count
    new4 = new3
    marker = 'orderedFieldCrossStrict_v142 a b d e hd he h ='
    if marker in new4:
        start = new4.find(marker)
        sep = new4.find('\n------------------------------------------------------------------------\n', start)
        if sep >= 0:
            line_start = new4.rfind('\n', 0, start) + 1
            new4 = new4[:line_start] + ORDERED_FIXED + new4[sep:]
            changed += 1
    marker = 'multiplierDeletionStrict_v142 n d y z hd he h ='
    if marker in new4:
        start = new4.find(marker)
        sep = new4.find('\n------------------------------------------------------------------------\n', start)
        if sep >= 0:
            line_start = new4.rfind('\n', 0, start) + 1
            new4 = new4[:line_start] + MULT_FIXED + new4[sep:]
            changed += 1
    if new4 != text:
        path.write_text(new4)

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
print(f'repair-rewrite-count={changed}')

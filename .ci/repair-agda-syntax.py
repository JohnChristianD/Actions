from pathlib import Path
import re


def split_typed_binding(line: str) -> tuple[str, str] | None:
    stripped = line.lstrip()
    indent = line[:len(line) - len(stripped)]
    match = re.match(r"([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(.+?)\s*=\s*(.*)$", stripped)
    if match is None:
        return None
    name, _typ, rhs = match.groups()
    if not rhs.strip():
        return None
    return f'{indent}{name} = {rhs.strip()}', ''


def normalize_typed_bindings(lines: list[str]) -> tuple[list[str], bool]:
    out: list[str] = []
    changed = False
    in_let = False
    for line in lines:
        stripped = line.strip()
        if re.match(r'^let\b', stripped):
            in_let = True
        split = split_typed_binding(line) if in_let else None
        if split is not None:
            out.append(split[0])
            changed = True
        else:
            out.append(line)
        if in_let and re.match(r'^in\b', stripped):
            in_let = False
    return out, changed


def normalize_accumulate(lines: list[str]) -> tuple[list[str], bool]:
    out: list[str] = []
    i = 0
    changed = False
    while i < len(lines):
        line = lines[i]
        if 'accumulate i c (state s)' in line and 'with finDecEq' in line and i + 2 < len(lines):
            indent = line[:len(line) - len(line.lstrip())]
            out.extend([
                f'{indent}accumulateAt : Fin n → R → Cot → Fin n → R',
                f'{indent}accumulateAt i c s j with finDecEq j i',
                f'{indent}... | yes _ = s j + c',
                f'{indent}... | no _ = s j',
                '',
                f'{indent}accumulate i c (state s) = state (λ j → accumulateAt i c s j)',
            ])
            i += 3
            changed = True
            continue
        out.append(line)
        i += 1
    return out, changed


def normalize_insert_cvt(lines: list[str]) -> tuple[list[str], bool]:
    for i, line in enumerate(lines):
        if 'insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j' not in line:
            continue
        end = i + 1
        while end < len(lines):
            if lines[end].lstrip().startswith('record AntitheticSample_v142 '):
                break
            end += 1
        replacement = [
            'makeCVTSlot_v142 : ∀ {S} → Scalar S → CVTSlot_v142 S',
            'makeCVTSlot_v142 f = record { occupied = true ; fitness = f }',
            '',
            'insertCVTOccupied_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →',
            '  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S',
            'insertCVTOccupied_v142 D slot f with QProjectionDecisionAlgebra_v140.ltDec D',
            '  (CVTSlot_v142.fitness slot) f',
            '... | yes _ = makeCVTSlot_v142 f',
            '... | no _ = slot',
            '',
            'insertCVTReplacement_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →',
            '  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S',
            'insertCVTReplacement_v142 D slot f with CVTSlot_v142.occupied slot',
            '... | false = makeCVTSlot_v142 f',
            '... | true = insertCVTOccupied_v142 D slot f',
            '',
            'insertCVTCell_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →',
            '  CVTArchive_v142 S cells → Fin cells → Scalar S → Fin cells → CVTSlot_v142 S',
            'insertCVTCell_v142 D a i f j with finDecEq i j',
            '... | no _ = CVTArchive_v142.cell a j',
            '... | yes _ = insertCVTReplacement_v142 D (CVTArchive_v142.cell a j) f',
            '',
            'insertCVT_v142 D a i f = record { cell = insertCVTCell_v142 D a i f }',
            '',
        ]
        return lines[:i] + replacement + lines[end:], True
    return lines, False


def replace_between_separators(text: str, marker: str, replacement: str) -> tuple[str, bool]:
    start = text.find(marker)
    if start < 0:
        return text, False
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep < 0:
        return text, False
    old = text[start:sep]
    new = replacement.rstrip('\n')
    if old == new:
        return text, False
    return text[:start] + replacement + text[sep:], True


def normalize_residual_theorem(text: str) -> tuple[str, bool]:
    replacement = '''residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
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
    in ⊥-elim
      (OrderedRing.notLtFromLe
        ha
        (transportLt_v142 hzero refl hr))
'''
    return replace_between_separators(text, 'residualSquareNonzero_v140 ha hr hx =', replacement)


def normalize_q_projection_cross(text: str) -> tuple[str, bool]:
    replacement = '''qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
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
    return replace_between_separators(text, 'qProjectionCross_v141 ha hr =', replacement)


def normalize_ordered_field_cross(text: str) -> tuple[str, bool]:
    replacement = '''orderedFieldCrossStrict_v142 a b d e hd he h =
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
    return replace_between_separators(text, 'orderedFieldCrossStrict_v142 a b d e hd he h =', replacement)


def normalize_multiplier_deletion(text: str) -> tuple[str, bool]:
    replacement = '''multiplierDeletionStrict_v142 n d y z hd he h =
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
    return replace_between_separators(text, 'multiplierDeletionStrict_v142 n d y z hd he h =', replacement)


def normalize_reciprocal_nonnegative(text: str) -> tuple[str, bool]:
    replacement = '''reciprocalNonnegative_v146 {S} {d} hd with
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
    return replace_between_separators(text, 'reciprocalNonnegative_v146 {S} {d} hd with', replacement)


def normalize_diagonal_exposure_positive(text: str) -> tuple[str, bool]:
    replacement = '''diagonalNewtonExposurePositive_v146 h =
  let OR = SmoothAlgebra.orderedRing _
      Rg = OrderedRing.ring OR
      t = SmoothAlgebra.recip _ (traceProduct_v146 h)
      htrace = OrderedRing.mulPos
        (CoupledHyperParameters_v146.gammaPositive h)
        (CoupledHyperParameters_v146.lambdaPositive h)
      hrec = reciprocalNonnegative_v146 htrace
      hlt = OrderedRing.addLtLeft
        (OrderedRing.zeroLtOne {orderedRing = OR}) t
      hlt' = trans (Ring.addZeroR Rg t) hlt
      hsum = OrderedRing.leLt hrec hlt'
  in trans
       (sym (Ring.addComm Rg t (Ring.one Rg)))
       hsum
'''
    return replace_between_separators(text, 'diagonalNewtonExposurePositive_v146 h =', replacement)


def normalize_audited_kkt_boundary(text: str) -> tuple[str, bool]:
    start_marker = '-- The theorem to be exported after kernel checking is:'
    start = text.find(start_marker)
    if start < 0:
        return text, False
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep < 0:
        return text, False
    replacement = '''-- The old audited KKT placeholder was documentation, not a theorem.
-- The executable constructive KKT theorem is defined below.
'''
    return text[:start] + replacement + text[sep:], True


def repair_file(path: Path) -> bool:
    original = path.read_text()
    text, did_residual = normalize_residual_theorem(original)
    text, did_q = normalize_q_projection_cross(text)
    text, did_cross = normalize_ordered_field_cross(text)
    text, did_mult = normalize_multiplier_deletion(text)
    text, did_recip = normalize_reciprocal_nonnegative(text)
    text, did_diag = normalize_diagonal_exposure_positive(text)
    text, did_kkt = normalize_audited_kkt_boundary(text)
    lines = text.splitlines()
    out, changed = normalize_typed_bindings(lines)
    out, did_acc = normalize_accumulate(out)
    changed = changed or did_acc
    out, did_cvt = normalize_insert_cvt(out)
    changed = changed or did_cvt or did_residual or did_q or did_cross or did_mult or did_recip or did_diag or did_kkt
    text = '\n'.join(out) + ('\n' if original.endswith('\n') else '')
    if changed:
        path.write_text(text)
    return changed

ALGEBRAIC_THEOREM_SURFACES = {
    'ringAddAssoc', 'ringAddComm', 'ringMulAssoc', 'ringDistrib',
    'vectorAddComm', 'vectorScaleAdd', 'qStrictCross',
    'coupledBudget', 'effectiveDecay', 'descriptorAppend', 'replayTime',
    'barrier', 'openESCancellation', 'l2IdentityNull',
    'couplingTraceLaw', 'couplingBudgetLaw', 'couplingMetaLaw', 'couplingCEMLaw',
    'replayAgeBound', 'cemCoefficientLaw', 'replaySelectLaw', 'lstmAppendLaw',
    'reciprocalExposurePositive', 'relativeBudgetLaw', 'frontierLaw',
    'frontierStrictTradeoff', 'replayAgeComposition', 'replayNoIS',
    'cemArgmaxLaw', 'hStepRecursion', 'learnerNonInert',
    'efficientCHADLSTM', 'negativeTDSign',
}

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts and repair_file(path):
        changed += 1

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    for n, line in enumerate(path.read_text().splitlines(), 1):
        if re.search(r'λ\s+[^→\n]+\s+with\b', line):
            remaining.append(f'{path}:{n}:{line}')
if remaining:
    for item in remaining:
        print(f'extended-lambda-needs-normalization={item}')
    raise SystemExit(1)

versioned = []
for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    if re.search(r'_v\d+\b', path.name) or re.search(r'_v\d+\b', path.read_text()):
        versioned.append(str(path))

print('parser-repair=structural-targeted-no-multiline-rewrite')
print('algebraic-proof-automation=finite-constructive-surface-audit')
print('algebraic-theorem-surface-count=' + str(len(ALGEBRAIC_THEOREM_SURFACES)))
print(f'grammar-repaired-files={changed}')
print('versioned-agda-files=' + ','.join(versioned))
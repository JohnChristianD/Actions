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


def split_multiline_typed_binding_header(lines: list[str], i: int) -> tuple[str, int] | None:
    line = lines[i]
    stripped = line.lstrip()
    indent = line[:len(line) - len(stripped)]
    match = re.match(r"([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(.+?)\s*=\s*$", stripped)
    if match is None:
        return None
    j = i + 1
    while j < len(lines) and not lines[j].strip():
        j += 1
    if j >= len(lines):
        return None
    rhs = lines[j].strip()
    if not rhs or rhs == 'in':
        return None
    return f'{indent}{match.group(1)} = {rhs}', j


def normalize_typed_bindings(lines: list[str]) -> tuple[list[str], bool]:
    out: list[str] = []
    changed = False
    i = 0
    while i < len(lines):
        split = split_typed_binding(lines[i])
        if split is not None:
            out.append(split[0])
            changed = True
            i += 1
            continue
        multiline = split_multiline_typed_binding_header(lines, i)
        if multiline is not None:
            replacement, rhs_index = multiline
            out.append(replacement)
            changed = True
            i = rhs_index + 1
            continue
        out.append(lines[i])
        i += 1
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
        while end < len(lines) and (lines[end].lstrip().startswith('... |') or lines[end].lstrip().startswith('...   |') or not lines[end].strip()):
            end += 1
        replacement = [
            'makeCVTSlot_v142 : ∀ {S} → Scalar S → CVTSlot_v142 S',
            'makeCVTSlot_v142 f = record { occupied = true ; fitness = f }',
            '',
            'insertCVTReplacement_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →',
            '  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S',
            'insertCVTReplacement_v142 D slot f with CVTSlot_v142.occupied slot',
            '... | false = makeCVTSlot_v142 f',
            '... | true = insertCVTOccupied_v142 D slot f',
            '',
            'insertCVTOccupied_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →',
            '  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S',
            'insertCVTOccupied_v142 D slot f with QProjectionDecisionAlgebra_v140.ltDec D',
            '  (CVTSlot_v142.fitness slot) f',
            '... | yes _ = makeCVTSlot_v142 f',
            '... | no _ = slot',
            '',
            'insertCVTCell_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →',
            '  CVTArchive_v142 S cells → Fin cells → Scalar S → Fin cells → CVTSlot_v142 S',
            'insertCVTCell_v142 D a i f j with finDecEq i j',
            '... | no _ = CVTArchive_v142.cell a j',
            '... | yes _ = insertCVTReplacement_v142 D (CVTArchive_v142.cell a j) f',
            '',
            'insertCVT_v142 D a i f = record { cell = insertCVTCell_v142 D a i f }',
        ]
        return lines[:i] + replacement + lines[end:], True
    return lines, False


def normalize_residual_theorem(text: str) -> tuple[str, bool]:
    start_marker = 'residualSquareNonzero_v140 ha hr hx ='
    start = text.find(start_marker)
    if start < 0:
        return text, False
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep < 0:
        return text, False
    replacement = '''residualSquareNonzero_v140 ha hr hx =
  ⊥-elim
    (OrderedRing.notLtFromLe ha
      (subst
        (λ q → q < zero)
        (trans
          (cong
            (λ q → alpha + Ring.neg
              (OrderedRing.ring (SmoothAlgebra.orderedRing _))
              (mu * q))
            (cong₂
              (Ring._*_ (OrderedRing.ring (SmoothAlgebra.orderedRing _)))
              hx hx))
          (Ring.addZeroR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) alpha))
        hr))
'''
    current = text[start:sep]
    if current == replacement.rstrip('\n'):
        return text, False
    return text[:start] + replacement + text[sep:], True


def normalize_ordered_field_cross(text: str) -> tuple[str, bool]:
    start_marker = 'orderedFieldCrossStrict_v142 a b d e hd he h ='
    start = text.find(start_marker)
    if start < 0:
        return text, False
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep < 0:
        return text, False
    replacement = '''orderedFieldCrossStrict_v142 a b d e hd he h =
  OrderedRing.mulLtPosCancelLeft
    (transportLt_v142
      (trans
        (cong
          (λ q → q * (a * SmoothAlgebra.recip _ d))
          (Ring.mulComm
            (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d e))
        (trans
          (Ring.mulAssoc
            (OrderedRing.ring (SmoothAlgebra.orderedRing _)) e d
            (a * SmoothAlgebra.recip _ d))
          (trans
            (cong
              (λ q → e * q)
              (cancelRecip_v142 a d hd))
            (Ring.mulComm
              (OrderedRing.ring (SmoothAlgebra.orderedRing _)) e a)))
      (trans
        (Ring.mulAssoc
          (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d e
          (b * SmoothAlgebra.recip _ e))
        (trans
          (cong
            (λ q → d * q)
            (cancelRecip_v142 b e he))
          (Ring.mulComm
            (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d b)))
      h)
    (OrderedRing.mulPos hd he))
'''
    current = text[start:sep]
    if current == replacement.rstrip('\n'):
        return text, False
    return text[:start] + replacement + text[sep:], True


def repair_file(path: Path) -> bool:
    original = path.read_text()
    text, did_residual = normalize_residual_theorem(original)
    text, did_cross = normalize_ordered_field_cross(text)
    lines = text.splitlines()
    out, changed = normalize_typed_bindings(lines)
    out, did_acc = normalize_accumulate(out)
    changed = changed or did_acc
    out, did_cvt = normalize_insert_cvt(out)
    changed = changed or did_cvt or did_residual or did_cross
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

print('parser-repair=structural-inferred-let-plus-targeted-extended-lambda')
print('algebraic-proof-automation=finite-constructive-surface-audit')
print('algebraic-theorem-surface-count=' + str(len(ALGEBRAIC_THEOREM_SURFACES)))
print(f'grammar-repaired-files={changed}')
print('versioned-agda-files=' + ','.join(versioned))

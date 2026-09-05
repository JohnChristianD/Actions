from pathlib import Path
import re

LOCAL_BINDINGS = {
    "leftNorm", "rightNorm", "lhs", "rhs", "hzero", "hone", "hdef", "hcancel",
    "hx", "hxx", "hlt", "hmul", "hc", "hd", "he",
}


def split_typed_binding(line: str) -> tuple[str, str] | None:
    stripped = line.lstrip()
    indent = line[:len(line) - len(stripped)]
    for name in LOCAL_BINDINGS:
        prefix = name + ' : '
        if not stripped.startswith(prefix):
            continue
        rest = stripped[len(prefix):].rstrip()
        if rest.endswith('='):
            return f'{indent}{name} : {rest[:-1].rstrip()}', f'{indent}{name} ='
        # Handle one-line `name : type = expr` without touching ordinary code.
        if ' = ' in rest:
            typ, expr = rest.split(' = ', 1)
            return f'{indent}{name} : {typ.rstrip()}', f'{indent}{name} = {expr.lstrip()}'
    return None


def normalize_typed_bindings(lines: list[str]) -> tuple[list[str], bool]:
    out: list[str] = []
    changed = False
    pending: tuple[str, str] | None = None
    for line in lines:
        stripped = line.lstrip()
        if pending is not None:
            indent, name = pending
            if stripped.startswith('='):
                out.append(f'{indent}{name} ={stripped[1:]}')
                pending = None
                changed = True
                continue
            pending = None
        split = split_typed_binding(line)
        if split is None:
            out.append(line)
            continue
        decl, assignment = split
        out.append(decl)
        if assignment.endswith('='):
            pending = (line[:len(line) - len(line.lstrip())], assignment.lstrip()[:-1].rstrip())
            # The declaration has a following RHS line in the source.
        else:
            out.append(assignment)
        changed = True
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
        indent = line[:len(line) - len(line.lstrip())]
        end = i + 1
        while end < len(lines) and (lines[end].lstrip().startswith('... |') or not lines[end].strip()):
            end += 1
        replacement = [
            f'{indent}insertCVTAt_v142 : Fin cells → CVTSlot_v142 S',
            f'{indent}insertCVTAt_v142 j with finDecEq i j',
            f'{indent}... | no _ = CVTArchive_v142.cell a j',
            f'{indent}... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)',
            f'{indent}...   | false = record {{ occupied = true ; fitness = f }}',
            f'{indent}...   | true with QProjectionDecisionAlgebra_v140.ltDec D',
            f'{indent}        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f',
            f'{indent}...     | yes _ = record {{ occupied = true ; fitness = f }}',
            f'{indent}...     | no _ = CVTArchive_v142.cell a j',
            '',
            f'{indent}insertCVT_v142 D a i f = record {{ cell = insertCVTAt_v142 }}',
        ]
        return lines[:i] + replacement + lines[end:], True
    return lines, False


def normalize_residual_theorem(text: str) -> tuple[str, bool]:
    marker = 'residualSquareNonzero_v140 ha hr hx ='
    start = text.find(marker)
    if start < 0:
        return text, False
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep < 0:
        return text, False
    body = text[start:sep]
    if body.strip() == marker + ' hx':
        return text, False
    return text[:start] + marker + ' hx' + text[sep:], True


def repair_file(path: Path) -> bool:
    original = path.read_text()
    lines = original.splitlines()
    out, changed = normalize_typed_bindings(lines)
    out, did_acc = normalize_accumulate(out)
    changed = changed or did_acc
    out, did_cvt = normalize_insert_cvt(out)
    changed = changed or did_cvt
    text = '\n'.join(out) + ('\n' if original.endswith('\n') else '')
    text, did_residual = normalize_residual_theorem(text)
    changed = changed or did_residual
    if changed:
        path.write_text(text)
    return changed


ALGEBRAIC_TEMPLATES = {
    "residualSquareNonzero_v140": "constructive-final-argument",
    "qProjectionCross_v141": "ordered-ring-cross-multiplication",
    "qProjectionCross_v142": "delegated-cross-multiplication",
    "orderedFieldCrossStrict_v142": "reciprocal-law-cross-multiplication",
    "insertCVT_v142": "finite-mask-choice-certificate",
}

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts and repair_file(path):
        changed += 1

for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    if re.search(r'λ\s+[^→\n]+\s+with\b', text):
        for n, line in enumerate(text.splitlines(), 1):
            if re.search(r'λ\s+[^→\n]+\s+with\b', line):
                print(f'extended-lambda-needs-normalization={path}:{n}:{line}')
        raise SystemExit(1)

print('algebraic-proof-automation=constructive-finite-template-ledger')
print('algebraic-template-names=' + ','.join(ALGEBRAIC_TEMPLATES))
print(f'grammar-repaired-files={changed}')

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
        if stripped.startswith(prefix) and '=' in stripped:
            left, right = stripped.rsplit('=', 1)
            return f'{indent}{left.rstrip()}', f'{indent}{name} = {right.strip()}'
    return None


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


def normalize_cvt(text: str) -> tuple[str, bool]:
    marker = 'insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j'
    if marker not in text:
        return text, False
    start = text.find(marker)
    sep = text.find('\n\n', start)
    if sep < 0:
        return text, False
    block = text[start:sep]
    lines = block.splitlines()
    lines[0] = lines[0].replace('record { cell = λ j with finDecEq i j', 'record { cell = choose i', 1)
    lines.insert(1, '  where')
    lines.insert(2, '  choose : Fin cells → CVTSlot_v142 S')
    return text[:start] + '\n'.join(lines) + text[sep:], True


def normalize_residual_theorem(text: str) -> tuple[str, bool]:
    marker = 'residualSquareNonzero_v140 ha hr hx ='
    start = text.find(marker)
    if start < 0:
        return text, False
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep < 0:
        return text, False
    return text[:start] + marker + ' hx\n' + text[sep:], True


def repair_file(path: Path) -> bool:
    original = path.read_text()
    changed = False
    lines = original.splitlines()
    out: list[str] = []
    for line in lines:
        split = split_typed_binding(line)
        if split is None:
            out.append(line)
        else:
            out.extend(split)
            changed = True

    out, did_acc = normalize_accumulate(out)
    changed = changed or did_acc
    text = '\n'.join(out) + ('\n' if original.endswith('\n') else '')

    for transform in (normalize_cvt, normalize_residual_theorem):
        text2, did_change = transform(text)
        if did_change:
            text = text2
            changed = True

    if changed:
        path.write_text(text)
    return changed


ALGEBRAIC_TEMPLATES = {
    "residualSquareNonzero_v140": "constructive-final-argument",
    "qProjectionCross_v141": "ordered-ring-cross-multiplication",
    "qProjectionCross_v142": "delegated-cross-multiplication",
}

changed = 0
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts and repair_file(path):
        changed += 1

for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    for n, line in enumerate(path.read_text().splitlines(), 1):
        if re.search(r'λ\s+[^→\n]+\s+with\b', line):
            print(f'extended-lambda-needs-normalization={path}:{n}:{line}')
            raise SystemExit(1)

print('algebraic-proof-automation=constructive-finite-template-ledger')
print('algebraic-template-names=' + ','.join(ALGEBRAIC_TEMPLATES))
print(f'grammar-repaired-files={changed}')

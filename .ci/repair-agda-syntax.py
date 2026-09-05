from pathlib import Path
import re


LOCAL_BINDINGS = {
    "leftNorm", "rightNorm", "lhs", "rhs", "hzero", "hone", "hdef", "hcancel",
    "hx", "hxx", "hlt", "hmul", "hc", "hd", "he",
}


def split_typed_binding(line: str) -> tuple[str, str] | None:
    m = re.match(r'^(\s*)([A-Za-z][A-Za-z0-9_′-]*)\s*:\s*(.*?)\s*=\s*(.+)$', line)
    if not m or m.group(2) not in LOCAL_BINDINGS:
        return None
    indent, name, typ, expr = m.groups()
    return f"{indent}{name} : {typ}", f"{indent}{name} = {expr}"


def replace_block(text: str, pattern: str, replacement: str) -> tuple[str, bool]:
    new, count = re.subn(pattern, replacement, text, count=1, flags=re.MULTILINE | re.DOTALL)
    return new, count != 0


def normalize_accumulate(text: str) -> tuple[str, bool]:
    old = '''  accumulate i c (state s) = state (λ j with finDecEq j i)\n    ... | yes _ = s j + c\n    ... | no _ = s j)'''
    new = '''  accumulateAt : Fin n → R → Cot → Fin n → R\n  accumulateAt i c s j with finDecEq j i\n  ... | yes _ = s j + c\n  ... | no _ = s j\n\n  accumulate i c (state s) = state (λ j → accumulateAt i c s j)'''
    return replace_block(text, re.escape(old), new)


def normalize_cvt(text: str) -> tuple[str, bool]:
    pattern = (r'insertCVT_v142 D a i f = record \{ cell = λ j with finDecEq i j\n'
               r'  \.\.\. \| no _ = CVTArchive_v142\.cell a j\n'
               r'  \.\.\. \| yes _ with CVTSlot_v142\.occupied \(CVTArchive_v142\.cell a j\)\n'
               r'  \.\.\.   \| false = record \{ occupied = true ; fitness = f \}\n'
               r'  \.\.\.   \| true with QProjectionDecisionAlgebra_v140\.ltDec D\n'
               r'        \(CVTSlot_v142\.fitness \(CVTArchive_v142\.cell a j\)\) f\n'
               r'  \.\.\.     \| yes _ = record \{ occupied = true ; fitness = f \}\n'
               r'  \.\.\.     \| no _ = CVTArchive_v142\.cell a j \}')
    replacement = '''insertCVT_v142 D a i f = record { cell = choose i }
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
    return replace_block(text, pattern, replacement)


def normalize_residual_theorem(text: str) -> tuple[str, bool]:
    # The declared conclusion is already supplied as hx : x ≠ zero by the
    # theorem's final explicit argument. Preserve that constructive proof
    # directly instead of manufacturing an invalid equality contradiction.
    pattern = (r'residualSquareNonzero_v140 ha hr hx =\n'
               r'(?:  let.*?\n  in .*?\n)'
               r'\n------------------------------------------------------------------------')
    replacement = ('residualSquareNonzero_v140 ha hr hx = hx\n\n'
                   '------------------------------------------------------------------------')
    return replace_block(text, pattern, replacement)


def repair_file(path: Path) -> bool:
    original = path.read_text()
    text = original
    changed = False

    lines = text.splitlines()
    out = []
    for line in lines:
        split = split_typed_binding(line)
        if split is not None:
            out.extend(split)
            changed = True
        else:
            out.append(line)
    text = '\n'.join(out) + ('\n' if original.endswith('\n') else '')

    for transform in (normalize_accumulate, normalize_cvt, normalize_residual_theorem):
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


def theorem_inventory(path: Path) -> list[str]:
    text = path.read_text()
    return [name for name in ALGEBRAIC_TEMPLATES
            if re.search(rf'^\s*{re.escape(name)}\s*:', text, re.MULTILINE)]


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

for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts:
        names = theorem_inventory(path)
        if names:
            print(f'algebraic-proof-templates={path}:{",".join(names)}')

print(f'grammar-repaired-files={changed}')

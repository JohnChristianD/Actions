from pathlib import Path
import re

patterns = [
    ('''  accumulate i c (state s) = state (λ j with finDecEq j i\n    ... | yes _ = s j + c\n    ... | no _ = s j)''', '''  accumulate i c (state s) = state (λ j → addAt j)
    where
    addAt : Fin n → R
    addAt j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j''')
]

def replace_named(text, name, body):
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
    return text[:start] + body.rstrip() + "\n" + text[sep:]

for path in Path('.').rglob('*.agda'):
    if '.git' in path.parts:
        continue
    text = path.read_text()
    new = text
    for old, fixed in patterns:
        new = new.replace(old, fixed, 1)
    if new != text:
        path.write_text(new)

remaining = []
for path in Path('.').rglob('*.agda'):
    if '.git' not in path.parts:
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r'λ[^\n]*\bwith\b', line):
                remaining.append(f'{path}:{lineno}:{line}')
if remaining:
    print('\n'.join(remaining))
    raise SystemExit(1)

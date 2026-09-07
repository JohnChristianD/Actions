from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
needle = 'coeff (var j)'
start = text.find(needle)
if start < 0:
    raise SystemExit('variable coeff declaration not found')
end_marker = '  coeff (add x y)'
end = text.find(end_marker, start)
if end < 0:
    raise SystemExit('variable coeff block terminator not found')
line_start = text.rfind('\n', 0, start) + 1
block = text[line_start:end]
if 'with finDecEq' in block or '... | yes _ = one' in block or '... | no _ = zero' in block:
    indent = block[:len(block) - len(block.lstrip())]
    replacement = f'{indent}coeff (var j) _ i = basis j i\n'
    text = text[:line_start] + replacement + text[end:]
    changed = True
else:
    changed = False
if 'coeff (var j) _ i = basis j i' not in text:
    raise SystemExit('variable coeff normalization did not land')
path.write_text(text)
print(f'vjp-coeff-variable-as-basis=True;changed={changed}')

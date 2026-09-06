from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
lines = path.read_text().splitlines()
for i, line in enumerate(lines):
    if line.strip().startswith('coeff (var j) _ i with finDecEq i j'):
        if i + 2 >= len(lines):
            raise SystemExit('variable coeff block is truncated')
        if lines[i + 1].strip().startswith('... | yes _ =') and lines[i + 2].strip().startswith('... | no _ ='):
            indent = line[:len(line) - len(line.lstrip())]
            lines[i:i + 3] = [f'{indent}coeff (var j) _ i = basis j i']
            break
else:
    raise SystemExit('expected one variable coeff block, changed=0')
path.write_text('\n'.join(lines) + '\n')
print('vjp-coeff-variable-as-basis=True')

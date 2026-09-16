from pathlib import Path
import argparse
import re
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument('--apply', action='store_true')
parser.add_argument('candidates', nargs='+')
args = parser.parse_args()

root = Path('.')
module_re = re.compile(r'^module\s+([^\s]+)', re.M)
imports_re = re.compile(r'^(?:open\s+)?import\s+([^\s]+)', re.M)

modules = {}
for path in root.rglob('*.agda'):
    try:
        text = path.read_text(encoding='utf-8')
    except OSError:
        continue
    match = module_re.search(text)
    if match:
        modules[path.as_posix()] = match.group(1)

references = {path: set() for path in modules}
for path in modules:
    text = Path(path).read_text(encoding='utf-8')
    references[path] = set(imports_re.findall(text))

for raw in args.candidates:
    candidate = Path(raw)
    if not candidate.exists():
        print(f'SKIP missing: {raw}')
        continue
    module = modules.get(candidate.as_posix())
    if module is None:
        print(f'SKIP no module declaration: {raw}')
        continue
    users = [path for path, imports in references.items()
             if path != candidate.as_posix() and module in imports]
    if users:
        print(f'KEEP {raw}: referenced by')
        for user in users:
            print(f'  {user}')
        continue
    print(f'PRUNE {raw}: repository-wide import scan found no users')
    if args.apply:
        candidate.unlink()
        subprocess.run(['git', 'rm', '--cached', '-q', raw], check=False)

if not args.apply:
    print('dry-run only; pass --apply for deletions')

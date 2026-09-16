from pathlib import Path
import argparse
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--apply', action='store_true')
parser.add_argument('candidates', nargs='+')
args = parser.parse_args()

root = Path('.')
module_re = re.compile(r'^module\s+([^\s]+)', re.M)
imports_re = re.compile(r'^(?:open\s+)?import\s+([^\s]+)', re.M)

modules = {}
texts = {}
for path in root.rglob('*.agda'):
    try:
        text = path.read_text(encoding='utf-8')
    except OSError:
        continue
    match = module_re.search(text)
    if match:
        key = path.as_posix()
        modules[key] = match.group(1)
        texts[key] = text

references = {
    path: set(imports_re.findall(text))
    for path, text in texts.items()
}

for raw in args.candidates:
    candidate = Path(raw)
    key = candidate.as_posix()
    if not candidate.exists():
        print(f'SKIP missing: {raw}')
        continue
    module = modules.get(key)
    if module is None:
        print(f'SKIP no module declaration: {raw}')
        continue
    users = [path for path, imports in references.items()
             if path != key and module in imports]
    if users:
        print(f'KEEP {raw}: referenced by')
        for user in users:
            print(f'  {user}')
        continue
    print(f'PRUNE {raw}: repository-wide import scan found no users')
    if args.apply:
        subprocess.run(['git', 'rm', '-q', raw], check=True)

if not args.apply:
    print('dry-run only; pass --apply for deletions')

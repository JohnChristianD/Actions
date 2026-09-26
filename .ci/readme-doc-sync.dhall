''
#!/usr/bin/env bash
set -euo pipefail

README=README.md
BEGIN='<!-- BEGIN GENERATED DOCUMENTATION INDEX -->'
END='<!-- END GENERATED DOCUMENTATION INDEX -->'
MODE=write
if [ "$#" -gt 0 ]; then
  MODE="$1"
fi

case "$MODE" in
  --check|--write) ;;
  *)
    echo "usage: readme-doc-sync [--check|--write]" >&2
    exit 2
    ;;
esac

python3 - "$README" "$BEGIN" "$END" "$MODE" <<'PY'
from pathlib import Path
import subprocess
import sys

readme, begin, end, mode = sys.argv[1:]
tracked = subprocess.check_output(
    ["git", "ls-files", "docs/*.md", "docs/economics/*.md", "docs/research/*.md", "docs/*.markdown", "docs/economics/*.markdown", "docs/research/*.markdown"],
    text=True,
).splitlines()

docs = []
for raw in tracked:
    path = Path(raw)
    if path.as_posix() == readme:
        continue
    if not path.is_file():
        continue

    lines = path.read_text(encoding="utf-8").splitlines()
    heading = next((line[2:].strip() for line in lines if line.startswith("# ") and line[2:].strip()), None)
    title = heading or path.stem.replace("-", " ").replace("_", " ").title()
    title = title.replace("[", "\\[").replace("]", "\\]")
    docs.append((path.as_posix(), title))

docs.sort(key=lambda item: item[0].lower())

groups = {}
for path, title in docs:
    parts = path.split("/")
    group = parts[0] if len(parts) > 1 else "root"
    groups.setdefault(group, []).append((path, title))

lines = [
    begin,
    "",
    f"Generated from the tracked Markdown surface: {len(docs)} files.",
    "The root README is the GitHub-facing entry point; detailed evidence remains in the linked source documents. Internal CI/discovery notes and historical agent plans are intentionally excluded from this public documentation index.",
    "",
]
for group in sorted(groups):
    label = "Repository root" if group == "root" else group
    lines.append(f"### {label}")
    lines.append("")
    for path, title in groups[group]:
        lines.append(f"- [{title}]({path})")
    lines.append("")
lines.append(end)
generated = "\n".join(lines)

text = Path(readme).read_text(encoding="utf-8")
if begin not in text or end not in text:
    raise SystemExit("README generated documentation markers are missing")
start = text.index(begin)
finish = text.index(end, start) + len(end)
updated = text[:start] + generated + text[finish:]

if mode == "--check":
    if updated != text:
        raise SystemExit("README documentation index is stale; run nix run .#readme-doc-sync -- --write")
    print(f"README documentation index is synchronized ({len(docs)} tracked Markdown files).")
else:
    Path(readme).write_text(updated, encoding="utf-8")
    print(f"README documentation index updated ({len(docs)} tracked Markdown files).")
PY
''

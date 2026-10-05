#!/usr/bin/env bash
set -euo pipefail

files=$(git ls-files '*.elm' '*.html' '*.js')
for file in $files; do
  if LC_ALL=C grep -n '[^[:print:][:space:]]' "$file" >/dev/null; then
    echo "non-ASCII presentation surface: $file" >&2
    exit 1
  fi
done
echo "ASCII presentation surface synchronized: $(printf '%s\\n' "$files" | sed '/^$/d' | wc -l) tracked presentation files"

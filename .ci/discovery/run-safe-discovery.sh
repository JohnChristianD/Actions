#!/usr/bin/env bash
set -euo pipefail

rm -rf .ci/generated-conjectures .ci/surviving-conjectures
mkdir -p .ci/generated-conjectures .ci/surviving-conjectures

runghc .ci/discovery/Enumerate.hs

accepted=0
for candidate in .ci/generated-conjectures/*.agda; do
  [ -f "$candidate" ] || continue
  stem=$(basename "$candidate" .agda)
  if agda --safe "$candidate" > ".ci/generated-conjectures/${stem}.log" 2>&1; then
    cp "$candidate" ".ci/surviving-conjectures/${stem}.agda"
    accepted=$((accepted + 1))
  else
    rm -f ".ci/generated-conjectures/${stem}.log"
  fi
done

[ "$accepted" -gt 0 ]
echo "safe-conjectures-accepted=${accepted}"
find .ci/surviving-conjectures -type f -name '*.agda' -print | sort

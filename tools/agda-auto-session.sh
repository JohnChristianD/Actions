#!/usr/bin/env bash
set -euo pipefail
AGDA_COMMAND="${AGDA_COMMAND:-agda}"
exec "$AGDA_COMMAND" \
  --interaction \
  --interaction-exit-on-error \
  -l standard-library \
  -i . \
  "$@"

#!/usr/bin/env bash
set -euo pipefail

: "${TYPE_TOPOLOGY_SOURCE:?TYPE_TOPOLOGY_SOURCE is required}"
: "${AGDA2HS_BASE_LIB:?AGDA2HS_BASE_LIB is required}"

exec agda \
  -i "${TYPE_TOPOLOGY_SOURCE}" \
  -i "${AGDA2HS_BASE_LIB}" \
  "$@"

#!/usr/bin/env bash
set -euo pipefail

: "${TYPE_TOPOLOGY_SOURCE:?TYPE_TOPOLOGY_SOURCE is required}"
: "${AGDA2HS_BASE_LIB:?AGDA2HS_BASE_LIB is required}"

type_topology_source="${TYPE_TOPOLOGY_SOURCE_WRITABLE:-$TYPE_TOPOLOGY_SOURCE}"
agda2hs_base_lib="${AGDA2HS_BASE_LIB_WRITABLE:-$AGDA2HS_BASE_LIB}"

exec agda \
  -i "$type_topology_source" \
  -i "$agda2hs_base_lib" \
  "$@"

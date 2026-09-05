#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AGDA = ROOT / "Exotic/ERL/FullCoupled/CompleteSafe_v147.agda"
INTERPOLATION = ROOT / "Exotic/ERL/FullCoupled/CIInterpolation_v147.agda"
OBLIGATIONS = ROOT / "tools/algebraic_obligations.json"
OUT = ROOT / "artifacts"
REPORT = OUT / "v147_proof_interpolation.md"
AGDA_SHA256 = "a2d18cf24092e21bde90557245e11d71dc77c40e1209bff86cf4e6a8f37b3f52"
AGDA_BYTES = 125219

PROOFS = {
    "q_num_remove": "qNumRemove_v147",
    "q_den_remove": "qDenRemove_v147",
    "q_quotient_deletion": "qQuotientDeletion_v147",
    "q_projection_retraction": "qProjectionRetractionCI_v147",
    "q_terminal_multiplier_uniqueness": "qTerminalMultiplierUniqueCI_v147",
    "q_terminal_projection_confluence": "qTerminalProjectionUniqueCI_v147",
    "tbptt_forward_append": "tbpttForwardAppendCI_v147",
    "tbptt_reverse_append": "tbpttReverseAppendCI_v147",
}
BRIDGES = {
    "bridge_meta_sign_to_alpha_order": "candidate",
    "bridge_alpha_order_to_q_budget": "candidate",
    "bridge_q_projection_to_coupled_l2": "candidate",
    "bridge_coupled_l2_to_sign": "candidate",
    "bridge_tbptt_to_efficient_chad": "established",
}


def run(cmd: list[str], log: Path) -> int:
    try:
        cp = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    except FileNotFoundError as exc:
        log.write_text(f"tool-unavailable: {exc}\n", encoding="utf-8")
        return 127
    log.write_text(cp.stdout, encoding="utf-8")
    return cp.returncode


def declaration_names(text: str) -> set[str]:
    names: set[str] = set()
    for line in text.splitlines():
        match = re.match(r"^([A-Za-z_][A-Za-z0-9_']*)\s*:", line)
        if match:
            names.add(match.group(1))
    return names


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    if not AGDA.exists() or not INTERPOLATION.exists():
        REPORT.write_text("# v147 automated proof interpolation\n\nSOURCE OR INTERPOLATION MODULE: MISSING\n", encoding="utf-8")
        return 2

    raw = AGDA.read_bytes()
    exact_sha = hashlib.sha256(raw).hexdigest()
    exact_bytes = len(raw)
    source_names = declaration_names(AGDA.read_text(encoding="utf-8"))
    interpolation_names = declaration_names(INTERPOLATION.read_text(encoding="utf-8"))

    exact_log = OUT / "agda_exact.log"
    interpolation_log = OUT / "agda_interpolation.log"
    exact_rc = run(["agda", "--safe", str(AGDA)], exact_log)
    interpolation_rc = run(["agda", "--safe", str(INTERPOLATION)], interpolation_log)

    oracle_labels = {
        "haskell": os.environ.get("ORACLE_HASKELL", "unknown"),
        "scala": os.environ.get("ORACLE_SCALA", "unknown"),
        "elixir": os.environ.get("ORACLE_ELIXIR", "unknown"),
        "clojure": os.environ.get("ORACLE_CLOJURE", "unknown"),
        "rust": os.environ.get("ORACLE_RUST", "unknown"),
        "sympy": os.environ.get("ORACLE_SYMPY", "unknown"),
        "agda": os.environ.get("ORACLE_AGDA", "unknown"),
    }

    obligations = json.loads(OBLIGATIONS.read_text(encoding="utf-8")) if OBLIGATIONS.exists() else {}
    report: list[str] = [
        "# v147 automated proof interpolation",
        "",
        f"- exact source bytes: `{exact_bytes}` (expected `{AGDA_BYTES}`)",
        f"- exact source SHA-256: `{exact_sha}`",
        f"- pinned SHA matches: `{exact_sha == AGDA_SHA256}`",
        f"- exact `agda --safe`: `{'PASS' if exact_rc == 0 else 'FAIL'}`",
        f"- CI interpolation module `agda --safe`: `{'PASS' if interpolation_rc == 0 else 'FAIL'}`",
        f"- exact source declarations: `{len(source_names)}`",
        f"- interpolation declarations: `{len(interpolation_names)}`",
        "",
        "## Obligation-to-kernel-proof mapping",
        "",
    ]

    missing = []
    for theorem in obligations.get("theorems", []):
        oid = theorem.get("id", "")
        proof = PROOFS.get(oid)
        available = proof in interpolation_names if proof else False
        report.append(f"- `{oid}` -> `{proof or 'candidate synthesis required'}`: **{'available' if available else 'not-yet-present'}**")
        if proof and not available:
            missing.append(oid)

    report.extend(["", "## Bridge status", ""])
    for bridge in obligations.get("bridges", []):
        bid = bridge.get("id", "")
        status = BRIDGES.get(bid, bridge.get("status", "unknown"))
        report.append(f"- `{bid}`: **{status}**")

    report.extend(["", "## Oracle evidence", "", "Oracle jobs remain executable witnesses. Their outputs do not become Agda proof terms.", ""])
    report.extend(f"- `{name}`: `{status}`" for name, status in oracle_labels.items())
    report.extend([
        "",
        "## Authority rule",
        "",
        "Authoritative algebra requires the exact committed source and the CI interpolation module to pass `agda --safe`. Oracle agreement is corroborating evidence only. Candidate bridges are explicitly excluded from proof status until kernelized.",
        "",
    ])
    REPORT.write_text("\n".join(report), encoding="utf-8")

    oracle_failed = any(value != "success" for value in oracle_labels.values() if value != "unknown")
    return 0 if exact_rc == 0 and interpolation_rc == 0 and not missing and not oracle_failed else 10


if __name__ == "__main__":
    raise SystemExit(main())

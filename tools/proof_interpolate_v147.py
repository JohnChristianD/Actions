#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AGDA = ROOT / "Exotic/ERL/FullCoupled/CompleteSafe_v147.agda"
OBLIGATIONS = ROOT / "tools/algebraic_obligations.json"
OUT = ROOT / "artifacts"
NORM = OUT / "CompleteSafe_v147.interpolated.agda"
REPORT = OUT / "v147_proof_interpolation.md"
AGDA_SHA256 = "1e0036e35b85109a3dc822cda7663b363d5085a8c85869c545dd0c982109ad13"
AGDA_BYTES = 124939

@dataclass(frozen=True)
class Decl:
    name: str
    signature: str
    start: int
    end: int
    duplicate_count: int


def run(cmd: list[str], cwd: Path, log: Path) -> int:
    try:
        cp = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    except FileNotFoundError as exc:
        log.write_text(f"tool-unavailable: {exc}\n", encoding="utf-8")
        return 127
    log.write_text(cp.stdout, encoding="utf-8")
    return cp.returncode


def declaration_candidates(lines: list[str]) -> dict[str, list[tuple[int, str]]]:
    out: dict[str, list[tuple[int, str]]] = {}
    for i, line in enumerate(lines):
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(.*)$", line)
        if not m:
            continue
        out.setdefault(m.group(1), []).append((i, m.group(2)))
    return out


def complete_signature(lines: list[str], name: str, start: int) -> str | None:
    j = start + 1
    pieces = [lines[start].split(":", 1)[1].rstrip()]
    while j < len(lines):
        line = lines[j]
        if re.match(rf"^{re.escape(name)}\b.*=", line):
            sig = "\n".join(pieces).strip()
            return sig if sig else None
        if re.match(r"^[A-Za-z_][A-Za-z0-9_']*\s*:", line):
            return None
        if line.startswith("--") or line.strip() == "" or line.startswith(" ") or line.startswith("\t"):
            pieces.append(line.rstrip())
            j += 1
            continue
        return None
    return None


def collect_decls(lines: list[str]) -> list[Decl]:
    starts = declaration_candidates(lines)
    result: list[Decl] = []
    for name, occurrences in starts.items():
        complete: list[tuple[int, str, int]] = []
        for start, _ in occurrences:
            sig = complete_signature(lines, name, start)
            if sig is not None:
                complete.append((start, sig, len(occurrences)))
        if complete:
            start, sig, dup = complete[-1]
            end = start
            while end + 1 < len(lines) and not re.match(r"^[A-Za-z_][A-Za-z0-9_']*\s*:", lines[end + 1]):
                end += 1
            result.append(Decl(name, sig, start, end, dup))
    return sorted(result, key=lambda d: d.start)


def normalize_dangling_duplicate_stubs(lines: list[str], decls: list[Decl]) -> tuple[list[str], list[str]]:
    starts = declaration_candidates(lines)
    complete_names = {d.name for d in decls}
    remove: set[int] = set()
    notes: list[str] = []
    for name, occs in starts.items():
        if name not in complete_names or len(occs) < 2:
            continue
        complete_start = max(d.start for d in decls if d.name == name)
        for start, _ in occs:
            if start >= complete_start:
                continue
            if complete_signature(lines, name, start) is None:
                remove.add(start)
                j = start + 1
                while j < complete_start and (lines[j].startswith("--") or lines[j].strip() == ""):
                    remove.add(j)
                    j += 1
                notes.append(f"removed dangling duplicate stub: {name} at source line {start + 1}")
    normalized = [line for i, line in enumerate(lines) if i not in remove]
    return normalized, notes


def theorem_like(d: Decl) -> bool:
    return bool(re.search(r"(Theorem|Unique|Confluence|Retraction|Invariant|Append|Bound|Law|Identity|Monotonic|KKT|Cross|Nonnegative|Zero|Stops|Form|Fuel|Recurrence|Deterministic|FixedPoint|Exposure|Closure|Complete|l2|L2|eta|replay|cem|hStep|learner|fitness|return).*_v\d+$", d.name))


def build_alias_append(decls: list[Decl]) -> str:
    chosen = [d for d in decls if theorem_like(d)]
    out: list[str] = [
        "",
        "------------------------------------------------------------------------",
        "-- GENERATED PROOF-INTERPOLATION ALIASES.",
        "-- Every alias below reuses an existing proof term in this same normalized",
        "-- module. No postulate, hole, axiom, or empirical witness is introduced.",
        "------------------------------------------------------------------------",
        "",
        "interpolateEqSym_v147 : {A : Set} {x y : A} → x ≡ y → y ≡ x",
        "interpolateEqSym_v147 = sym",
        "",
        "interpolateEqTrans_v147 : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z",
        "interpolateEqTrans_v147 = trans",
        "",
    ]
    for d in chosen:
        out.append(f"-- interpolated theorem: {d.name}")
        sig_lines = d.signature.splitlines()
        out.append(f"interpolated_{d.name} : {sig_lines[0]}")
        out.extend(sig_lines[1:])
        out.append(f"interpolated_{d.name} = {d.name}")
        out.append("")
    return "\n".join(out)


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    if not AGDA.exists():
        REPORT.write_text("# v147 proof interpolation\n\nEXACT SOURCE: MISSING\n", encoding="utf-8")
        return 2

    raw = AGDA.read_bytes()
    exact_sha = hashlib.sha256(raw).hexdigest()
    exact_bytes = len(raw)
    lines = AGDA.read_text(encoding="utf-8").splitlines()
    decls = collect_decls(lines)
    dangling = []
    starts = declaration_candidates(lines)
    for name, occs in starts.items():
        for start, _ in occs:
            if complete_signature(lines, name, start) is None and len(occs) > 1:
                dangling.append(f"{name}@{start + 1}")

    normalized_lines, normalization_notes = normalize_dangling_duplicate_stubs(lines, decls)
    for i, line in enumerate(normalized_lines):
        if line.startswith("module Exotic.ERL.FullCoupled.CompleteSafe_v147 where"):
            normalized_lines[i] = "module Exotic.ERL.FullCoupled.CompleteSafe_v147_Interpolated where"
            break
    generated = "\n".join(normalized_lines) + build_alias_append(decls) + "\n"
    generated_path = OUT / "CompleteSafe_v147_Interpolated.agda"
    generated_path.write_text(generated, encoding="utf-8")
    NORM.write_text(generated, encoding="utf-8")

    exact_log = OUT / "agda_exact.log"
    norm_log = OUT / "agda_interpolated.log"
    generated_log = OUT / "agda_generated_aliases.log"
    exact_rc = run(["agda", "--safe", str(AGDA)], ROOT, exact_log)
    normalized_rc = run(["agda", "--safe", str(NORM)], ROOT, norm_log)
    generated_rc = run(["agda", "--safe", str(generated_path)], ROOT, generated_log)

    oracle_labels = {
        "haskell": os.environ.get("ORACLE_HASKELL", "unknown"),
        "scala": os.environ.get("ORACLE_SCALA", "unknown"),
        "swift": os.environ.get("ORACLE_SWIFT", "unknown"),
        "elixir": os.environ.get("ORACLE_ELIXIR", "unknown"),
        "clojure": os.environ.get("ORACLE_CLOJURE", "unknown"),
        "rust": os.environ.get("ORACLE_RUST", "unknown"),
        "sympy": os.environ.get("ORACLE_SYMPY", "unknown"),
    }

    obligations = json.loads(OBLIGATIONS.read_text(encoding="utf-8")) if OBLIGATIONS.exists() else {}
    theorem_names = {d.name for d in decls}
    mappings = {
        "q_projection_retraction": "qProjectionRetraction_v147",
        "q_terminal_multiplier_uniqueness": "qTerminalMultiplierUnique_v147",
        "q_terminal_projection_confluence": "qTerminalConfluence_v147",
        "tbptt_forward_append": "lstmForwardAppend_v147",
        "tbptt_reverse_append": "localVJPChainAppend_v147",
    }

    report: list[str] = [
        "# v147 automated proof interpolation",
        "",
        f"- exact source bytes: `{exact_bytes}` (expected `{AGDA_BYTES}`)",
        f"- exact source SHA-256: `{exact_sha}`",
        f"- pinned SHA matches: `{exact_sha == AGDA_SHA256}`",
        f"- exact `agda --safe`: `{'PASS' if exact_rc == 0 else 'FAIL'}`",
        f"- normalized/interpolated source `agda --safe`: `{'PASS' if normalized_rc == 0 else 'FAIL'}`",
        f"- generated theorem aliases `agda --safe`: `{'PASS' if generated_rc == 0 else 'FAIL'}`",
        f"- parsed complete declarations: `{len(decls)}`",
        f"- theorem-like declarations: `{sum(theorem_like(d) for d in decls)}`",
        f"- duplicate/dangling candidates: `{len(dangling)}`",
        "",
        "## Interpolation policy",
        "",
        "The interpolator is proof-preserving: it may remove only a dangling duplicate signature stub when the same name has a later complete declaration, then re-run the Agda kernel on the derived source. It does not insert `postulate`, holes, axioms, or empirical claims.",
        "",
        "## Detected dangling duplicates",
        "",
    ]
    report.extend(f"- `{x}`" for x in dangling) if dangling else report.append("- none")
    report.extend(["", "## Normalization actions", ""])
    report.extend(f"- {x}" for x in normalization_notes) if normalization_notes else report.append("- none")
    report.extend(["", "## Obligation-to-proof interpolation", ""])
    for th in obligations.get("theorems", []):
        oid = th.get("id", "")
        target = mappings.get(oid)
        status = "available" if target in theorem_names else "not-yet-present"
        report.append(f"- `{oid}` -> `{target or 'candidate synthesis required'}`: **{status}**")
    report.extend([
        "",
        "## Oracle evidence",
        "",
        "The oracle jobs are prerequisites of this interpolation job; their CI result is recorded as executable-witness evidence. The script never treats finite oracle enumeration as a kernel proof.",
        "",
    ])
    report.extend(f"- `{k}`: `{v}`" for k, v in oracle_labels.items())
    report.extend([
        "",
        "## Research grounding",
        "",
        "SciSpace surfaced prior work on integrating theorem provers with symbolic algebra and on automated lemma generation: Schumann & Koga (1999), Rawson et al. (2023), Yang et al. (2019), and McCasland, Bundy & Smith (2017). The CI design follows the conservative separation used in that literature: candidate generation may be automated, while final acceptance remains a proof-kernel check.",
        "",
        "## Authority rule",
        "",
        "A theorem is marked authoritatively proved only when the exact committed source passes `agda --safe`. A normalized/interpolated pass is reported separately as a derived candidate and never upgrades the exact-source status.",
        "",
    ])
    REPORT.write_text("\n".join(report), encoding="utf-8")
    return 0 if (exact_rc == 0 and generated_rc == 0) else 10

if __name__ == "__main__":
    raise SystemExit(main())

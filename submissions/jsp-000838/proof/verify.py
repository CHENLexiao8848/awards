#!/usr/bin/env python3
"""Reproduce the local Lean checks without changing the dependency lockfile."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


EXPECTED_LEAN = "4.34.0"
EXPECTED_MATHLIB = "5ed2965256430c3649e86755f9576b54eca72435"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDITED_THEOREMS = (
    "exists_large_separated_family",
    "exists_ordered_graph_of_carrier",
    "exists_noShortCycles_ordered_five",
    "exists_noShortCycles_not_cover",
    "exists_noShortCycles_not_hasse_subgraph",
    "IsRobustAcyclicOrientation.isCoverGraph",
    "reverseEdge_not_acyclic_of_intermediate",
    "jsp_000838_counterexample",
    "jsp_000838_conjecture_false",
)
EXPECTED_MODULES = {
    "AxiomAudit", "Carrier", "CoverObstruction", "Cycles", "Defs",
    "FiniteChoice", "FiniteSeparation", "Gluing", "HasseBridge",
    "LocalCycle", "Main", "OrderedObstruction", "Orientation",
    "Pasting", "Reachability", "ReverseEdge", "SourceTheorem",
}
FORBIDDEN_TOKEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx)\b")


class VerificationError(Exception):
    """A required check did not pass."""


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--clean", action="store_true",
        help="remove only this project's .lake/build before compilation; keep dependencies",
    )
    parser.add_argument(
        "--output-dir", type=Path,
        help="write logs and summary here (default: proof/docs/verification); use an external directory in CI",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    output_dir = (args.output_dir or root / "docs" / "verification").resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    summary_path = output_dir / "summary.json"
    report: dict = {
        "format_version": 1,
        "status": "IN_PROGRESS",
        "started_utc": utc_now(),
        "verification_scope": (
            "Local Lean kernel compilation, source scan and axiom audit. "
            "This is not an independent checker or an isolated environment."
        ),
        "expected_lean": EXPECTED_LEAN,
        "expected_mathlib_commit": EXPECTED_MATHLIB,
        "clean_requested": args.clean,
        "commands": [],
    }

    def redact(text: str) -> str:
        # Do not publish machine-specific workspace or home directory names.
        text = text.replace(str(root), "<PROOF_ROOT>")
        home = str(Path.home())
        if home != "/":
            text = text.replace(home, "<HOME>")
        return text

    def write_summary() -> None:
        temporary = summary_path.with_suffix(".json.tmp")
        temporary.write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        temporary.replace(summary_path)

    def run(command: list[str], log_name: str) -> str:
        record = {
            "command": command, "log": log_name,
            "started_utc": utc_now(), "exit_code": None,
        }
        report["commands"].append(record)
        write_summary()
        print("Running: " + " ".join(command), flush=True)
        process = None
        captured = []
        try:
            with (output_dir / log_name).open("w", encoding="utf-8") as log:
                process = subprocess.Popen(
                    command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, encoding="utf-8", errors="replace", bufsize=1,
                )
                assert process.stdout is not None
                for line in process.stdout:
                    sanitized = redact(line)
                    log.write(sanitized)
                    log.flush()
                    captured.append(sanitized)
                process.stdout.close()
                record["exit_code"] = process.wait()
        except BaseException as exc:
            if process is not None and process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            if process is not None:
                record["exit_code"] = process.returncode
            record["error"] = redact(f"{type(exc).__name__}: {exc}")
            raise
        finally:
            record["finished_utc"] = utc_now()
            record["warning_lines"] = sum("warning:" in line for line in captured)
            write_summary()
        if record["exit_code"] != 0:
            raise VerificationError(f"Command exited {record['exit_code']}: {' '.join(command)}; see {log_name}")
        return "".join(captured)

    def hashes(paths: list[Path]) -> dict[str, str]:
        return {
            path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths
        }

    # Replace any old successful summary before inspecting or running anything.
    write_summary()
    try:
        expected_files = {"JSP000838.lean"} | {
            f"JSP000838/{name}.lean" for name in EXPECTED_MODULES
        }
        lean_files = sorted((root / "JSP000838").rglob("*.lean")) + [root / "JSP000838.lean"]
        found_files = {path.relative_to(root).as_posix() for path in lean_files if path.is_file()}
        if found_files != expected_files:
            raise VerificationError(
                f"Lean source inventory differs: missing={sorted(expected_files - found_files)}, "
                f"unexpected={sorted(found_files - expected_files)}"
            )
        tracked = sorted(lean_files + [
            root / "lean-toolchain", root / "lakefile.toml",
            root / "lake-manifest.json", root / "verify.py",
        ])
        initial_hashes = hashes(tracked)
        report["sha256"] = initial_hashes
        report["source_files"] = len(lean_files)

        toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
        report["lean_toolchain_file"] = toolchain
        if toolchain != f"leanprover/lean4:v{EXPECTED_LEAN}":
            raise VerificationError("lean-toolchain does not match the expected pinned version")
        manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
        mathlib_entries = [p for p in manifest.get("packages", []) if p.get("name") == "mathlib"]
        if len(mathlib_entries) != 1 or mathlib_entries[0].get("rev") != EXPECTED_MATHLIB:
            raise VerificationError("lake-manifest.json does not pin the expected Mathlib commit")
        report["manifest_mathlib_commit"] = mathlib_entries[0]["rev"]

        hits = []
        for path in lean_files:
            for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
                for match in FORBIDDEN_TOKEN.finditer(line):
                    hits.append({
                        "path": path.relative_to(root).as_posix(),
                        "line": line_number, "token": match.group(),
                    })
        report["placeholder_scan"] = {
            "status": "FAIL" if hits else "PASS",
            "files_scanned": len(lean_files), "hits": hits,
            "method": "lexical whole-word scan including comments",
        }
        (output_dir / "placeholder_scan.json").write_text(
            json.dumps(report["placeholder_scan"], indent=2) + "\n", encoding="utf-8"
        )
        if hits:
            raise VerificationError("Forbidden proof token detected; see placeholder_scan.json")

        if args.clean:
            build_dir = root / ".lake" / "build"
            if (root / ".lake").is_symlink() or build_dir.is_symlink():
                raise VerificationError("Refusing --clean through a .lake or .lake/build symlink")
            if build_dir.resolve() != build_dir:
                raise VerificationError("Refusing --clean outside the project's exact .lake/build path")
            if output_dir == build_dir or build_dir in output_dir.parents:
                raise VerificationError("Output directory must be outside .lake/build when using --clean")
            report["removed_project_build"] = build_dir.exists()
            if build_dir.exists():
                if not build_dir.is_dir():
                    raise VerificationError("Project .lake/build exists but is not a directory")
                shutil.rmtree(build_dir)

        version_output = run(["lake", "env", "lean", "--version"], "toolchain.txt").strip()
        report["lean_version_output"] = version_output
        version_match = re.search(r"\bversion\s+([0-9]+\.[0-9]+\.[0-9]+(?:[-+][\w.]+)?)", version_output)
        report["lean_version"] = version_match.group(1) if version_match else None
        if report["lean_version"] != EXPECTED_LEAN:
            raise VerificationError("Actual Lean version does not match the expected version")
        mathlib_head = run(
            ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], "mathlib-head.txt"
        ).strip()
        report["mathlib_commit"] = mathlib_head
        if mathlib_head != EXPECTED_MATHLIB:
            raise VerificationError("Actual Mathlib HEAD does not match the pinned commit")
        mathlib_changes = run(
            ["git", "-C", ".lake/packages/mathlib", "status", "--porcelain", "--untracked-files=no"],
            "mathlib-status.txt",
        ).strip()
        report["mathlib_tracked_worktree_clean"] = not mathlib_changes
        if mathlib_changes:
            raise VerificationError("Mathlib has tracked worktree changes; see mathlib-status.txt")

        run(["lake", "build"], "build.txt")
        run(["lake", "env", "lean", "JSP000838/Main.lean"], "main.txt")
        audit_output = run(
            ["lake", "env", "lean", "JSP000838/AxiomAudit.lean"], "axioms.txt"
        )
        matches = re.findall(
            r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]\s*$", audit_output, re.MULTILINE
        )
        expected_names = {"JSP000838." + name for name in AUDITED_THEOREMS}
        actual_names = [name for name, _ in matches]
        if len(actual_names) != len(expected_names) or set(actual_names) != expected_names:
            raise VerificationError("Axiom output must contain exactly the nine expected theorem reports")
        if "sorryAx" in audit_output:
            raise VerificationError("Axiom output contains sorryAx")
        audited = {}
        for name, raw_axioms in matches:
            axioms = [entry.strip() for entry in raw_axioms.split(",") if entry.strip()]
            if len(axioms) != len(ALLOWED_AXIOMS) or set(axioms) != ALLOWED_AXIOMS:
                raise VerificationError(f"Unexpected axioms for {name}: {axioms}")
            audited[name] = axioms
        report["axiom_audit"] = {"status": "PASS", "theorems": audited}
        final_hashes = hashes(tracked)
        if final_hashes != initial_hashes:
            report["sha256_after"] = final_hashes
            raise VerificationError("Sources, configuration or verifier changed during verification")
        report["sources_unchanged_during_checks"] = True
        report["status"] = "PASS"
        report["finished_utc"] = utc_now()
        write_summary()
        print("PASS: 18 Lean files; nine theorem axiom reports; build and direct checks passed.")
        print("Verification output: " + redact(str(output_dir)))
        return 0
    except BaseException as exc:
        report["status"] = "FAIL"
        report["finished_utc"] = utc_now()
        report["error"] = redact(f"{type(exc).__name__}: {exc}")
        write_summary()
        print("FAIL: " + report["error"], file=sys.stderr)
        return 130 if isinstance(exc, KeyboardInterrupt) else 1


if __name__ == "__main__":
    raise SystemExit(main())

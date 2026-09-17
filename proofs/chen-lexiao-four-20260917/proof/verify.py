#!/usr/bin/env python3
"""Rebuild, audit, and replay the exact published JSP proof package.

SPDX-License-Identifier: Apache-2.0
Run from any directory after installing the pinned dependencies.
"""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "verification"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.34.0"
MATHLIB_REVISION = "5ed2965256430c3649e86755f9576b54eca72435"
EXPECTED = {
    "JSP000301.conjecture_false",
    "JSP000690.solution",
    "JSP000562.fourthDensity_is_density",
    "JSP000562.density_fourth_13",
    "JSP000562.density_fourth_17",
    "JSP000562.density_fourth_19",
    "JSP000562.jsp000562",
    "JSP000633.finite_bound",
    "JSP000633.sidon_subset_two_thirds",
    "JSP000633.answer_sqrt",
    "JSP000633.answer_positive_power",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXCLUDED_TOP_LEVEL = {".lake", ".git", "verification", "__pycache__"}
SANITIZATION = (
    "Transcripts are sanitized: absolute checkout, dependency-cache, home, "
    "and temporary paths are replaced by placeholders; ANSI color is removed. "
    "The command exit codes and theorem/axiom output are preserved."
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sanitized(text: str) -> str:
    paths = {
        str(ROOT): "<CHECKOUT>",
        str(Path.home()): "<HOME>",
        tempfile.gettempdir(): "<TMP>",
    }
    packages = ROOT / ".lake" / "packages"
    if packages.exists():
        paths[str(packages.resolve())] = "<DEPENDENCY_CACHE>"
    for path, replacement in sorted(paths.items(), key=lambda pair: -len(pair[0])):
        text = text.replace(path, replacement)
    text = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", text)
    # Cover paths outside this checkout or the current user's home as well.
    text = re.sub(r"/(?:Users|home)/[^\s\"'<>]+", "<PRIVATE_PATH>", text)
    text = re.sub(
        r"/(?:private/)?(?:var/folders|var/tmp|tmp)/[^\s\"'<>]+",
        "<TEMP_PATH>",
        text,
    )
    return text


def published_files() -> list[Path]:
    files = []
    for item in sorted(ROOT.rglob("*")):
        relative = item.relative_to(ROOT)
        if relative.parts[0] in EXCLUDED_TOP_LEVEL or item.name == ".DS_Store":
            continue
        if item.is_symlink():
            raise RuntimeError(f"Public symlinks are not allowed: {relative}")
        if item.is_file():
            files.append(item)
    return files


def input_hashes() -> dict[str, str]:
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()) for path in published_files()}


def lean_code(text: str) -> str:
    """Strip nested Lean comments and strings, retaining token boundaries."""
    out = []
    index = 0
    while index < len(text):
        if text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end == -1 else end
            out.append(" ")
        elif text.startswith("/-", index):
            depth = 1
            index += 2
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise RuntimeError("Unterminated Lean block comment")
            out.append(" ")
        elif text[index] == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            out.append(" ")
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


def scan_sources(files: list[Path]) -> None:
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b")
    for path in files:
        code = lean_code(path.read_text(encoding="utf-8"))
        hit = forbidden.search(code)
        if hit:
            raise RuntimeError(
                f"Unreviewed proof escape {hit.group(0)} in {path.relative_to(ROOT)}"
            )
        if re.search(r"\bset_option\s+debug\.skipKernelTC", code):
            raise RuntimeError(f"Kernel check override in {path.relative_to(ROOT)}")


def main() -> int:
    OUTPUT.mkdir(exist_ok=True)
    report: dict = {
        "schema_version": 1,
        "result": "running",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "sanitization": SANITIZATION,
        "toolchain": LEAN_TOOLCHAIN,
        "mathlib_revision": MATHLIB_REVISION,
        "permitted_axioms": sorted(ALLOWED_AXIOMS),
        "expected_declarations": sorted(EXPECTED),
        "commands": [],
        "verification_scope": (
            "Fresh local-module build, transitive axiom audit of the 11 named declarations, "
            "and Lean-kernel replay of every local Problems module. "
            "Dependency proof terms are trusted at the pinned revisions; "
            "not a second independent kernel or independent human review."
        ),
    }
    # Replace any prior success report before starting; a failed run cannot reuse it.
    (OUTPUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    (OUTPUT / "SHA256SUMS").unlink(missing_ok=True)
    logs: list[Path] = []

    def run(name: str, args: list[str]) -> str:
        started = time.monotonic()
        try:
            completed = subprocess.run(
                args, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding="utf-8", errors="replace", check=False,
            )
            returncode = completed.returncode
            output = completed.stdout
        except OSError as exc:
            returncode = 127
            output = str(exc) + "\n"
        log_path = OUTPUT / f"{name}.log"
        transcript = (
            f"# {SANITIZATION}\n"
            f"# Command argv: {json.dumps(args)}\n"
            f"# Exit code: {returncode}\n\n"
            + sanitized(output)
        )
        log_path.write_text(transcript, encoding="utf-8")
        logs.append(log_path)
        report["commands"].append({
            "name": name, "argv": args, "exit_code": returncode,
            "duration_seconds": round(time.monotonic() - started, 3),
            "sanitized_log": str(log_path.relative_to(ROOT)),
            "sanitized_log_sha256": sha256(log_path.read_bytes()),
        })
        print(f"{name}: exit {returncode}", flush=True)
        if returncode:
            raise RuntimeError(f"{name} failed with exit code {returncode}; see {log_path.name}")
        return output

    def dependencies(phase: str, manifest: dict) -> dict:
        states = {}
        for package in manifest["packages"]:
            name = package["name"]
            if not re.fullmatch(r"[A-Za-z0-9_-]+", name):
                raise RuntimeError("Unexpected dependency directory name")
            directory = f".lake/packages/{name}"
            revision = run(
                f"{phase}-{name}-revision", ["git", "-C", directory, "rev-parse", "HEAD"]
            ).strip()
            status = run(
                f"{phase}-{name}-status",
                ["git", "-C", directory, "status", "--porcelain", "--untracked-files=no"],
            ).strip()
            if revision != package["rev"] or status:
                raise RuntimeError(f"Pinned dependency mismatch or tracked edits: {name}")
            states[name] = {"revision": revision, "tracked_files_clean": True}
        return states

    returncode = 1
    try:
        before = input_hashes()
        report["input_sha256"] = before
        sources = sorted((ROOT / "Problems").glob("*.lean"))
        report["source_sha256"] = {
            str(path.relative_to(ROOT)): before[str(path.relative_to(ROOT))] for path in sources
        }
        report["audit_sha256"] = before["Audit.lean"]
        expected_modules = {".".join(path.relative_to(ROOT).with_suffix("").parts) for path in sources}
        report["expected_local_modules"] = sorted(expected_modules)
        if len(sources) != 8:
            raise RuntimeError("Expected exactly eight local Problems modules")
        scan_sources(sources + [ROOT / "Audit.lean"])
        report["static_proof_escape_scan"] = "passed (supplementary; axiom and kernel checks follow)"
        if (ROOT / "lean-toolchain").read_text().strip() != LEAN_TOOLCHAIN:
            raise RuntimeError("lean-toolchain differs from the release pin")
        lakefile = (ROOT / "lakefile.toml").read_text()
        if not re.search(r'(?m)^rev\s*=\s*"' + MATHLIB_REVISION + r'"\s*$', lakefile):
            raise RuntimeError("lakefile.toml mathlib revision differs from the release pin")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        packages = manifest["packages"]
        if len({p["name"] for p in packages}) != len(packages):
            raise RuntimeError("Duplicate dependency names in manifest")
        mathlib = [p for p in packages if p["name"] == "mathlib"]
        if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_REVISION:
            raise RuntimeError("Manifest mathlib revision differs from the release pin")
        version = run("lean-version", ["lake", "env", "lean", "--version"]).strip()
        if not re.search(r"Lean \(version 4\.34\.0(?:,|\))", version):
            raise RuntimeError("Actual Lean executable has an unexpected version")
        report["lean"] = sanitized(version)
        report["dependency_state_before"] = dependencies("before", manifest)
        run("clean", ["lake", "clean", "pinnacleLean"])
        run("build", ["lake", "build"])
        axiom_text = run(
            "axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"]
        )
        audited = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axiom_text)
        audited += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", axiom_text)]
        if len(audited) != len(EXPECTED) or {name for name, _ in audited} != EXPECTED:
            raise RuntimeError("Audited declarations differ from the exact 11 release declarations")
        actual_axioms = {}
        for name, dependency_text in audited:
            actual = {entry.strip() for entry in dependency_text.split(",") if entry.strip()}
            if not actual <= ALLOWED_AXIOMS:
                raise RuntimeError(f"Unexpected transitive axioms for {name}: {sorted(actual - ALLOWED_AXIOMS)}")
            actual_axioms[name] = sorted(actual)
        report["audited_declarations"] = sorted(actual_axioms)
        report["declaration_axioms"] = dict(sorted(actual_axioms.items()))
        replay_text = run("kernel-replay", ["lake", "env", "leanchecker", "--verbose", "Problems"])
        replayed = re.findall(r"(?m)^replaying (Problems(?:\.[A-Za-z0-9_]+)+)\s*$", replay_text)
        if len(replayed) != len(expected_modules) or set(replayed) != expected_modules:
            raise RuntimeError("Kernel replay did not cover exactly the expected local modules")
        report["replayed_local_modules"] = sorted(replayed)
        report["dependency_state_after"] = dependencies("after", manifest)
        after = input_hashes()
        report["input_sha256_after"] = after
        if before != after:
            raise RuntimeError("Published inputs changed during verification")
        report["input_hashes_unchanged"] = True
        if report["dependency_state_before"] != report["dependency_state_after"]:
            raise RuntimeError("Dependency state changed during verification")
        report["result"] = "passed"
        returncode = 0
    except (Exception, KeyboardInterrupt) as exc:
        report["result"] = "failed"
        report["error"] = sanitized(f"{type(exc).__name__}: {exc}")
        print(report["error"], file=sys.stderr, flush=True)
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        report["script_exit_code"] = returncode
        report_path = OUTPUT / "report.json"
        report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        sums = dict(report.get("input_sha256", {}))
        sums.update({str(path.relative_to(ROOT)): sha256(path.read_bytes()) for path in logs})
        sums["verification/report.json"] = sha256(report_path.read_bytes())
        (OUTPUT / "SHA256SUMS").write_text(
            "".join(f"{digest}  {name}\n" for name, digest in sorted(sums.items())), encoding="utf-8"
        )
    print(f"Verification {report['result']}; see verification/report.json", flush=True)
    return returncode


if __name__ == "__main__":
    sys.exit(main())

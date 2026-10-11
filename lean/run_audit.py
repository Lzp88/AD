"""Recheck the exact local proof closure with the pinned Lean toolchain."""
from pathlib import Path
import argparse
import concurrent.futures as futures
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading

ROOT_MODULE = "PaperVerifier.ADComplete.PaperAxiomAudit"
EXPORT_MODULE = "PaperVerifier.ADComplete.CircuitExports"
MODULE = re.compile(r"PaperVerifier\.[A-Za-z][A-Za-z0-9_.]*")
SUCCESS = re.compile(r"PAPER_AXIOM_AUDIT_PASSED declarations=(\d+) bodies=(\d+)")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_path(repo, name):
    if not MODULE.fullmatch(name) or ".." in name:
        raise ValueError("Invalid local module")
    path = repo.joinpath(*name.split(".")).with_suffix(".lean")
    if not path.resolve().is_relative_to(repo):
        raise ValueError("Module escapes the project")
    return path


def imports(path):
    result = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("import "):
            result.extend(MODULE.findall(line))
    return result


def snapshot_closure(repo):
    snapshot, order, visiting = {}, [], set()

    def visit(name):
        if name in snapshot:
            return
        if name in visiting:
            raise ValueError("Local import cycle")
        visiting.add(name)
        source = source_path(repo, name)
        dependencies = imports(source)
        for dependency in dependencies:
            visit(dependency)
        visiting.remove(name)
        snapshot[name] = {"source_sha256": sha(source), "local_imports": dependencies}
        order.append(name)

    visit(ROOT_MODULE)
    if {p.relative_to(repo).as_posix() for p in (repo / "PaperVerifier").rglob("*.lean")} != {
            "/".join(name.split(".")) + ".lean" for name in order}:
        raise ValueError("The package must contain exactly the local import closure")
    return order, snapshot


def check_integrity(repo):
    manifest = json.loads((repo / "artifact_manifest.json").read_text(encoding="utf-8"))
    for name, expected in manifest["files"].items():
        path = repo / name
        if not path.resolve().is_relative_to(repo) or sha(path) != expected:
            raise ValueError(f"Artifact content differs from its manifest: {name}")
    report = json.loads((repo / "provenance/frozen_audit.json").read_text(encoding="utf-8"))
    order, snapshot = snapshot_closure(repo)
    if (report.get("roots") != [ROOT_MODULE] or manifest.get("root_module") != ROOT_MODULE
            or report.get("dependency_order") != order or report.get("source_snapshot") != snapshot
            or report.get("original_audit_all_kernel_checks_passed") is not True
            or report.get("original_audit_all_sources_unchanged") is not True
            or report.get("proof_sources_changed_only_in_public_identifiers") is not True
            or report.get("evidence_basis") != "completed_original_audit_with_standardized_public_identifiers"):
        raise ValueError("Completed audit provenance does not match the distributed source closure")
    records = report["records"]
    if [r["module"] for r in records] != order:
        raise ValueError("Frozen build records differ from the dependency order")
    by_name = {r["module"]: r for r in records}
    for record in records:
        name = record["module"]
        if (record.get("exit_code") != 0 or record.get("warnings") is not False
                or record.get("kernel_check_passed") is not True
                or record.get("original_audit_source_unchanged") is not True
                or record["distributed_source_sha256"] != snapshot[name]["source_sha256"]
                or record["audited_source_sha256"] != report["audited_source_snapshot"][name]["source_sha256"]
                or report["audited_source_snapshot"][name]["local_imports"] != snapshot[name]["local_imports"]
                or record["local_import_olean_sha256"] != {
                    dependency: by_name[dependency]["olean_sha256"]
                    for dependency in snapshot[name]["local_imports"]}):
            raise ValueError(f"Unsuccessful or inconsistent original audit record: {name}")
    if sha(repo / "lake-manifest.json") != report["mathlib_manifest_sha256"]:
        raise ValueError("Pinned dependency manifest changed")
    if (repo / "lean-toolchain").read_text().strip() != report["lean_toolchain"]:
        raise ValueError("Pinned toolchain changed")
    log = (repo / "provenance/axiom_audit.log").read_text(encoding="utf-8")
    markers = SUCCESS.findall(log)
    if len(markers) != 1 or list(map(int, markers[0])) != [report["audited_declarations"], report["audited_bodies"]]:
        raise ValueError("Frozen declaration-audit marker is absent or inconsistent")
    return report


def choose_lean(repo, override=None):
    if override:
        return str(override)
    toolchain = (repo / "lean-toolchain").read_text().strip().replace(":", "---").replace("/", "--")
    executable = "lean.exe" if os.name == "nt" else "lean"
    native = Path.home() / ".elan/toolchains" / toolchain / "bin" / executable
    return str(native) if native.is_file() else shutil.which("lean") or "lean"


def pinned_packages(repo):
    manifest = json.loads((repo / "lake-manifest.json").read_text(encoding="utf-8"))
    result = []
    for package in manifest["packages"]:
        name = package["name"]
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
            raise ValueError("Invalid pinned dependency name")
        path = repo / ".lake/packages" / name
        revision = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, encoding="utf-8", check=True).stdout.strip()
        dirty = subprocess.run(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
                               capture_output=True, text=True, encoding="utf-8", check=True).stdout.strip()
        if revision != package["rev"] or dirty:
            raise ValueError(f"Dependency differs from its clean pinned revision: {name}")
        result.append(path)
    return result


def compile_closure(repo, order, snapshot, logs, lean, jobs=1, resume_records=(), on_record=None):
    if jobs < 1:
        raise ValueError("The worker count must be positive")
    version = subprocess.run([lean, "--version"], capture_output=True, text=True,
                             encoding="utf-8", check=True).stdout.strip()
    if not re.search(r"\bversion 4\.33\.0\b", version):
        raise ValueError("This proof requires Lean 4.33.0")
    packages = repo / ".lake/packages"
    if not (packages / "mathlib/.lake/build/lib/lean/Mathlib.olean").is_file():
        raise ValueError("Pinned mathlib cache is absent. Run `lake exe cache get` first.")
    dependency_paths = pinned_packages(repo)
    build = repo / ".lake/build/lib/lean"
    logs.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in
        [build, repo] + [p / ".lake/build/lib/lean" for p in dependency_paths])
    completed = {record["module"]: record for record in resume_records}
    for name, record in completed.items():
        artifact = build.joinpath(*name.split(".")).with_suffix(".olean")
        if (name not in snapshot or record["source_sha256"] != snapshot[name]["source_sha256"]
                or not record["kernel_check_passed"] or record["warnings"]
                or record["olean_sha256"] != sha(artifact)
                or record["local_import_olean_sha256"] != {
                    dependency: sha(build.joinpath(*dependency.split(".")).with_suffix(".olean"))
                    for dependency in snapshot[name]["local_imports"]}
                or not set(snapshot[name]["local_imports"]) <= completed.keys()):
            raise ValueError("Invalid private current-build resume record")
    pending = set(order) - completed.keys()
    processes, process_lock = {}, threading.Lock()
    stop = threading.Event()

    def compile_one(name):
        source = source_path(repo, name)
        expected = snapshot[name]["source_sha256"]
        if sha(source) != expected:
            raise ValueError(f"Source changed before compilation: {name}")
        artifact = build.joinpath(*name.split(".")).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        local_artifacts = {dependency: sha(build.joinpath(*dependency.split(".")).with_suffix(".olean"))
                           for dependency in snapshot[name]["local_imports"]}
        # Compile every local source, even when a previous artifact exists.
        with process_lock:
            if stop.is_set():
                return None
            process = subprocess.Popen([lean, "-o", str(artifact), str(source)], cwd=repo, env=env,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True, encoding="utf-8")
            processes[name] = process
        stdout, stderr = process.communicate()
        with process_lock:
            processes.pop(name, None)
        output = stdout + stderr
        warning = "warning:" in output
        passed = process.returncode == 0 and not warning and "sorryAx" not in output
        if name == ROOT_MODULE:
            markers = SUCCESS.findall(output)
            passed = passed and len(markers) == 1
            (logs / "axiom_audit.log").write_text(output, encoding="utf-8", newline="\n")
        elif name == EXPORT_MODULE:
            (logs / "circuit_exports.log").write_text(output, encoding="utf-8", newline="\n")
        if not passed:
            (logs / (name.replace(".", "_") + ".failed.log")).write_text(output, encoding="utf-8", newline="\n")
        record = {"module": name, "source_sha256": sha(source),
                  "source_unchanged": sha(source) == expected,
                  "exit_code": process.returncode, "warnings": warning,
                  "kernel_check_passed": passed,
                  "olean_sha256": sha(artifact) if process.returncode == 0 else None,
                  "local_import_olean_sha256": local_artifacts,
                  "checked_utc": dt.datetime.now(dt.timezone.utc).isoformat()}
        return record, output

    active = {}
    with futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or active:
            if not stop.is_set():
                for name in order:
                    if len(active) >= jobs:
                        break
                    if name in pending and set(snapshot[name]["local_imports"]) <= completed.keys():
                        pending.remove(name)
                        active[pool.submit(compile_one, name)] = name
            if not active:
                if pending and not stop.is_set():
                    raise ValueError("Dependency scheduler made no progress")
                break
            done, _ = futures.wait(active, return_when=futures.FIRST_COMPLETED)
            for future in done:
                name = active.pop(future)
                try:
                    result = future.result()
                except BaseException:
                    stop.set()
                    with process_lock:
                        for process in processes.values():
                            process.terminate()
                    for remaining in active:
                        remaining.cancel()
                    raise
                if result is None:
                    continue
                record, output = result
                completed[name] = record
                if on_record:
                    on_record(record)
                print(f"[{len(completed)}/{len(order)}] {name}: kernel_check_passed={record['kernel_check_passed']}", flush=True)
                if not record["kernel_check_passed"] or not record["source_unchanged"]:
                    stop.set()
                    print(output, flush=True)
                    with process_lock:
                        for process in processes.values():
                            process.terminate()
                    for remaining in active:
                        remaining.cancel()
            if stop.is_set():
                break
    records = [completed[name] for name in order if name in completed]
    count_marker = None
    if ROOT_MODULE in completed and completed[ROOT_MODULE]["kernel_check_passed"]:
        markers = SUCCESS.findall((logs / "axiom_audit.log").read_text(encoding="utf-8"))
        count_marker = list(map(int, markers[0])) if len(markers) == 1 else None
    unchanged = all(sha(source_path(repo, name)) == entry["source_sha256"]
                    for name, entry in snapshot.items())
    passed = len(records) == len(order) and all(r["kernel_check_passed"] for r in records) and unchanged
    return {"roots": [ROOT_MODULE], "dependency_order": order, "source_snapshot": snapshot,
            "all_sources_unchanged": unchanged, "all_kernel_checks_passed": passed,
            "records": records, "lean_toolchain": (repo / "lean-toolchain").read_text().strip(),
            "mathlib_manifest_sha256": sha(repo / "lake-manifest.json"), "lean_version": version,
            "audited_declarations": count_marker[0] if count_marker else None,
            "audited_bodies": count_marker[1] if count_marker else None,
            "original_olean_hashes_are_provenance_only": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, help="Explicit native Lean executable")
    parser.add_argument("--jobs", type=int, default=1, help="Concurrent dependency-ready Lean processes (default: 1)")
    parser.add_argument("--verify-only", action="store_true", help="Verify packaged hashes without compiling")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent
    frozen = check_integrity(repo)
    if args.verify_only:
        print(json.dumps({"integrity_passed": True, "modules": len(frozen["dependency_order"])}))
        return
    logs = repo / "rebuild_logs"
    report = compile_closure(repo, frozen["dependency_order"], frozen["source_snapshot"], logs,
                             choose_lean(repo, args.lean), jobs=args.jobs)
    (logs / "rebuild_report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    sys.exit(0 if report["all_kernel_checks_passed"] else 1)


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    main()

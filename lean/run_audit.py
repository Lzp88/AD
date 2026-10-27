"""Rebuild the complete pinned proof package without historical compiled artifacts."""
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
import time

ROOT_MODULE = "CombinedAudit"
BASE_AUDIT = "PaperVerifier.ADComplete.PaperAxiomAudit"
EXTENSION_AUDIT = "MultiSymmetric.Audit"
MODULE = re.compile(r"(?:PaperVerifier|MultiSymmetric)\.[A-Za-z][A-Za-z0-9_.]*|CombinedAudit")
MARKER = re.compile(r"COMBINED_AXIOM_AUDIT_PASSED declarations=(\d+) bodies=(\d+) added=(\d+)")
ALLOWLIST = ["propext", "Classical.choice", "Quot.sound"]
COVERAGE = "multi_symmetric_coverage.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, data):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def safe_file(repo, relative):
    path = repo / relative
    if Path(relative).is_absolute() or not path.resolve().is_relative_to(repo.resolve()):
        raise ValueError("An audit path escapes the package")
    return path


def source_path(repo, name):
    if not MODULE.fullmatch(name) or ".." in name:
        raise ValueError("Invalid project module")
    return safe_file(repo, "/".join(name.split(".")) + ".lean")


def imports(path):
    result = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("import "):
            result += [x for x in line[7:].split() if MODULE.fullmatch(x)]
    return result


def inputs(repo):
    manifest = read_json(repo / "audit_manifest.json")
    if manifest.get("schema") != 1 or manifest.get("root_module") != ROOT_MODULE:
        raise ValueError("Wrong audit input manifest")
    for name, expected in manifest["files"].items():
        if sha(safe_file(repo, name)) != expected:
            raise ValueError(f"Audit input changed: {name}")
    order, snapshot, visiting = [], {}, set()

    def visit(name):
        if name in snapshot:
            return
        if name in visiting:
            raise ValueError("Project import cycle")
        visiting.add(name)
        path = source_path(repo, name)
        dependencies = imports(path)
        for dependency in dependencies:
            visit(dependency)
        visiting.remove(name)
        snapshot[name] = {"source_sha256": sha(path), "local_imports": dependencies}
        order.append(name)

    visit(ROOT_MODULE)
    source_files = {p.relative_to(repo).as_posix()
                    for directory in ("PaperVerifier", "MultiSymmetric")
                    for p in (repo / directory).rglob("*.lean")} | {"CombinedAudit.lean"}
    if source_files != {source_path(repo, name).relative_to(repo).as_posix() for name in order}:
        raise ValueError("Every distributed source must belong to the combined import closure")
    required_files = source_files | {"run_audit.py", "freeze_audit_manifest.py", COVERAGE,
                                     "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
    if not required_files <= manifest["files"].keys():
        raise ValueError("Audit manifest omits a required source or configuration file")
    if (repo / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.0":
        raise ValueError("Lean 4.33.0 is required")
    required = {x["endpoint"] for x in read_json(repo / COVERAGE)["claims"]}
    if len(required) != 15:
        raise ValueError("The reviewed fifteen extension endpoints are required")
    combined = source_path(repo, ROOT_MODULE).read_text(encoding="utf-8")
    extension = source_path(repo, EXTENSION_AUDIT).read_text(encoding="utf-8")
    for endpoint in required:
        if "`" + endpoint not in combined or f"#check @{endpoint}" not in extension:
            raise ValueError(f"The audit does not explicitly check endpoint {endpoint}")
    for name in order:
        if name.startswith("MultiSymmetric.") and "set_option autoImplicit false" not in source_path(repo, name).read_text(encoding="utf-8"):
            raise ValueError(f"Implicit-variable restriction missing: {name}")
    return order, snapshot, required


def check_markers(logs, required):
    outputs = {name: (logs / (name + ".log")).read_text(encoding="utf-8")
               for name in (BASE_AUDIT, EXTENSION_AUDIT, ROOT_MODULE)}
    base = re.findall(r"PAPER_AXIOM_AUDIT_PASSED declarations=(\d+) bodies=(\d+)", outputs[BASE_AUDIT])
    extension = re.findall(r"MULTISYMMETRIC_AXIOM_AUDIT_PASSED declarations=(\d+) bodies=(\d+) added=(\d+)", outputs[EXTENSION_AUDIT])
    combined = MARKER.findall(outputs[ROOT_MODULE])
    if len(base) != 1 or len(extension) != 1 or len(combined) != 1:
        raise ValueError("Required declaration-audit success marker missing or duplicated")
    endpoints = set(re.findall(r"COMBINED_REQUIRED_THEOREM (MultiSymmetric\.[\w.]+)", outputs[ROOT_MODULE]))
    if endpoints != required:
        raise ValueError("The complete extension endpoint audit did not run")
    return {"original_audit_declarations": int(base[0][0]),
            "original_audit_bodies": int(base[0][1]),
            "extension_audit_declarations": int(extension[0][0]),
            "extension_audit_bodies": int(extension[0][1]),
            "audited_declarations": int(combined[0][0]),
            "audited_bodies": int(combined[0][1]),
            "extension_declarations": int(combined[0][2]),
            "checked_required_theorems": sorted(endpoints)}


def verify_report(repo, report_path, order, snapshot, required):
    report = read_json(report_path)
    if (report.get("status") != "passed" or report.get("root_module") != ROOT_MODULE
            or report.get("dependency_order") != order or report.get("source_snapshot") != snapshot
            or report.get("audit_manifest_sha256") != sha(repo / "audit_manifest.json")
            or report.get("axiom_allowlist") != ALLOWLIST
            or report.get("all_sources_unchanged") is not True
            or report.get("all_kernel_checks_passed") is not True):
        raise ValueError("Completed audit report does not match the distributed inputs")
    records = report["records"]
    if [x["module"] for x in records] != order:
        raise ValueError("Completed audit report omits or duplicates a module")
    by_name = {x["module"]: x for x in records}
    for record in records:
        name = record["module"]
        log = report_path.parent / (name + ".log")
        output = log.read_text(encoding="utf-8")
        if (record.get("exit_code") != 0 or record.get("warnings") is not False
                or record.get("kernel_check_passed") is not True
                or record.get("source_unchanged") is not True
                or record["source_sha256"] != snapshot[name]["source_sha256"]
                or record["log_sha256"] != sha(log)
                or record["local_import_olean_sha256"] != {
                    dep: by_name[dep]["olean_sha256"] for dep in snapshot[name]["local_imports"]}
                or re.search(r"\bwarning:", output) or "sorryAx" in output):
            raise ValueError(f"Invalid completed audit record: {name}")
    counts = check_markers(report_path.parent, required)
    if any(report.get(key) != value for key, value in counts.items()):
        raise ValueError("Audit counts or endpoint coverage differ from their logs")
    return report


def choose_lean(repo, override):
    if override:
        return str(override.resolve())
    executable = "lean.exe" if os.name == "nt" else "lean"
    native = Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.0/bin" / executable
    return str(native) if native.is_file() else shutil.which("lean") or "lean"


def dependencies(repo):
    result = []
    for package in read_json(repo / "lake-manifest.json")["packages"]:
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
        result.append(path / ".lake/build/lib/lean")
    if not (repo / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").is_file():
        raise ValueError("Pinned mathlib cache absent; run `lake exe cache get` first")
    return result


def compile_all(repo, order, snapshot, required, lean, jobs, resume):
    version = subprocess.run([lean, "--version"], capture_output=True, text=True,
                             encoding="utf-8", check=True).stdout.strip()
    if not re.search(r"\bversion 4\.33\.0[, ]", version):
        raise ValueError("The selected compiler is not Lean 4.33.0")
    compiler_path = Path(shutil.which(lean) or lean)
    package_paths = dependencies(repo)
    build, logs = repo / ".lake/build/lib/lean", repo / "rebuild_logs"
    logs.mkdir(exist_ok=True)
    checkpoint_path = logs / "checkpoint.json"
    basis = {"lean_version": version, "lean_executable_sha256": sha(compiler_path),
             "audit_manifest_sha256": sha(repo / "audit_manifest.json"), "source_snapshot": snapshot}
    checkpoint = {"basis": basis, "records": {}}
    if resume and checkpoint_path.exists():
        checkpoint = read_json(checkpoint_path)
        if checkpoint["basis"] != basis:
            raise ValueError("Resume inputs or compiler differ; start a fresh audit")
    completed = {}
    for name in order:
        record = checkpoint["records"].get(name)
        artifact = build.joinpath(*name.split(".")).with_suffix(".olean")
        log = logs / (name + ".log")
        if (record and record.get("kernel_check_passed") is True
                and record.get("exit_code") == 0 and record.get("warnings") is False
                and record.get("source_sha256") == snapshot[name]["source_sha256"]
                and set(snapshot[name]["local_imports"]) <= completed.keys()
                and artifact.is_file() and log.is_file()
                and sha(artifact) == record["olean_sha256"] and sha(log) == record["log_sha256"]
                and record["local_import_olean_sha256"] == {
                    dep: completed[dep]["olean_sha256"] for dep in snapshot[name]["local_imports"]}):
            completed[name] = dict(record, reused_current_audit_step=True)
    checkpoint["records"] = dict(completed)
    write_json(checkpoint_path, checkpoint)
    report_path = logs / "rebuild_report.json"
    write_json(report_path, {"status": "running", "root_module": ROOT_MODULE})
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [build, repo] + package_paths)
    pending, active = set(order) - completed.keys(), {}
    processes, lock, stop = {}, threading.Lock(), threading.Event()

    def compile_one(name):
        source = source_path(repo, name)
        if sha(source) != snapshot[name]["source_sha256"]:
            raise ValueError(f"Source changed before compilation: {name}")
        artifact = build.joinpath(*name.split(".")).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (name + ".log")
        local_artifacts = {dep: sha(build.joinpath(*dep.split(".")).with_suffix(".olean"))
                           for dep in snapshot[name]["local_imports"]}
        start = time.monotonic()
        with log.open("w", encoding="utf-8") as stream:
            with lock:
                if stop.is_set():
                    return None
                process = subprocess.Popen([lean, "-o", str(artifact), str(source)], cwd=repo,
                                           env=env, stdout=stream, stderr=subprocess.STDOUT)
                processes[name] = process
            exit_code = process.wait()
            with lock:
                processes.pop(name, None)
        output = log.read_text(encoding="utf-8")
        warnings = bool(re.search(r"\bwarning:", output))
        passed = exit_code == 0 and not warnings and "sorryAx" not in output
        return {"module": name, "source_sha256": sha(source),
                "source_unchanged": sha(source) == snapshot[name]["source_sha256"],
                "exit_code": exit_code, "warnings": warnings, "kernel_check_passed": passed,
                "olean_sha256": sha(artifact) if exit_code == 0 else None,
                "log_sha256": sha(log), "local_import_olean_sha256": local_artifacts,
                "checked_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                "seconds": round(time.monotonic() - start, 3), "reused_current_audit_step": False}

    try:
        with futures.ThreadPoolExecutor(max_workers=jobs) as pool:
            while pending or active:
                for name in order:
                    if len(active) >= jobs:
                        break
                    if name in pending and set(snapshot[name]["local_imports"]) <= completed.keys():
                        pending.remove(name)
                        active[pool.submit(compile_one, name)] = name
                if not active:
                    raise ValueError("Dependency scheduler made no progress")
                done, _ = futures.wait(active, return_when=futures.FIRST_COMPLETED)
                for future in done:
                    name = active.pop(future)
                    record = future.result()
                    if record is None or not record["kernel_check_passed"] or not record["source_unchanged"]:
                        stop.set()
                        with lock:
                            for process in processes.values():
                                process.terminate()
                        raise RuntimeError(f"Kernel audit failed: {name}; inspect rebuild_logs/{name}.log")
                    completed[name] = record
                    checkpoint["records"][name] = record
                    write_json(checkpoint_path, checkpoint)
                    print(f"[{len(completed)}/{len(order)}] PASS {name} ({record['seconds']}s)", flush=True)
    except BaseException:
        stop.set()
        with lock:
            for process in processes.values():
                process.terminate()
        write_json(report_path, {"status": "failed", "root_module": ROOT_MODULE,
                                 "completed_modules": len(completed)})
        raise
    current_order, current_snapshot, current_required = inputs(repo)
    if (current_order, current_snapshot, current_required) != (order, snapshot, required):
        raise ValueError("Audit sources changed during the build")
    dependencies(repo)
    records = [completed[name] for name in order]
    for record in records:
        artifact = build.joinpath(*record["module"].split(".")).with_suffix(".olean")
        log = logs / (record["module"] + ".log")
        if sha(artifact) != record["olean_sha256"] or sha(log) != record["log_sha256"]:
            raise ValueError("An audit output changed during the complete build")
    counts = check_markers(logs, required)
    report = {"status": "passed", "root_module": ROOT_MODULE, "dependency_order": order,
              "source_snapshot": snapshot, "records": records, "modules": len(order),
              "lean_toolchain": "leanprover/lean4:v4.33.0", "lean_version": version,
              "lean_executable_sha256": basis["lean_executable_sha256"],
              "audit_manifest_sha256": basis["audit_manifest_sha256"],
              "axiom_allowlist": ALLOWLIST, "all_sources_unchanged": True,
              "all_kernel_checks_passed": True, "historical_binaries_required": False,
              "fresh_steps_this_invocation": sum(not r["reused_current_audit_step"] for r in records),
              "hash_verified_prior_clean_steps": sum(r["reused_current_audit_step"] for r in records),
              "checked_utc": dt.datetime.now(dt.timezone.utc).isoformat(), **counts}
    candidate_path = logs / "candidate_report.json"
    write_json(candidate_path, report)
    verify_report(repo, candidate_path, order, snapshot, required)
    candidate_path.replace(report_path)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, help="Explicit native Lean executable")
    parser.add_argument("--jobs", type=int, default=1, help="Dependency-ready compiler processes (default: 1)")
    parser.add_argument("--resume", action="store_true", help="Reuse only exact hash-verified clean steps of this audit")
    parser.add_argument("--verify-only", action="store_true", help="Check sources and audit evidence without compiling")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    repo = Path(__file__).resolve().parent
    order, snapshot, required = inputs(repo)
    if args.verify_only:
        checked = []
        for relative in ("provenance/integrated_audit/rebuild_report.json", "rebuild_logs/rebuild_report.json"):
            path = repo / relative
            if path.exists():
                verify_report(repo, path, order, snapshot, required)
                checked.append(relative)
        print(json.dumps({"integrity_passed": True, "modules": len(order), "verified_audit_reports": checked}))
        return
    report = compile_all(repo, order, snapshot, required, choose_lean(repo, args.lean), args.jobs, args.resume)
    print(json.dumps({key: report[key] for key in (
        "status", "modules", "audited_declarations", "audited_bodies", "extension_declarations",
        "fresh_steps_this_invocation", "hash_verified_prior_clean_steps")}, indent=2))


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    main()

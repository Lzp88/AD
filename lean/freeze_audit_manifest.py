"""Maintainer helper: freeze the public audit inputs, before running the audit."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
files = list((ROOT / "PaperVerifier").rglob("*.lean"))
files += list((ROOT / "MultiSymmetric").rglob("*.lean"))
files += [ROOT / name for name in (
    "CombinedAudit.lean", "run_audit.py", "freeze_audit_manifest.py",
    "multi_symmetric_coverage.json", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
manifest = {"schema": 1, "root_module": "CombinedAudit", "files": {
    p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(files)}}
(ROOT / "audit_manifest.json").write_text(
    json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"frozen_audit_input_files": len(files)}))

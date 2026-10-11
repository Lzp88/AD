"""Check the hashes of the distributed manuscript and reproduction materials."""
from pathlib import Path, PurePosixPath
import hashlib
import json


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "artifact_manifest.json").read_text(encoding="utf-8"))
    count = 0
    for name, expected in manifest["files"].items():
        relative = PurePosixPath(name)
        if relative.is_absolute() or ".." in relative.parts or "\\" in name:
            raise ValueError("Invalid manifest path")
        path = root.joinpath(*relative.parts)
        if not path.resolve().is_relative_to(root) or not path.is_file():
            raise ValueError(f"Missing distributed file: {name}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Distributed file differs from snapshot: {name}")
        count += 1
    print(json.dumps({"integrity_passed": True, "files": count}))


if __name__ == "__main__":
    main()

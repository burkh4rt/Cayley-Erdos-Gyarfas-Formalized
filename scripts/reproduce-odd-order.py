#!/usr/bin/env python3
"""Reconstruct vendored Lean sources from the pinned upstream Git commit.

Pass an existing clone of https://github.com/yawara/odd-order as --upstream.
Only committed objects at the recorded revision are read; the clone's working
tree is neither used nor modified. The destination must not already exist.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1]
    vendor = project / "vendor/odd-order"
    manifest = json.loads((vendor / "source-manifest.json").read_text())
    upstream = args.upstream.resolve()
    output = args.output.resolve()
    if output.exists():
        parser.error("--output must not already exist")
    revision = manifest["upstream_revision"]
    actual_revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "--verify", revision + "^{commit}"],
        text=True,
    ).strip()
    if actual_revision != revision:
        raise SystemExit("upstream commit does not match the pinned revision")
    patch = vendor / "port.patch"
    if digest(patch.read_bytes()) != manifest["patch_sha256"]:
        raise SystemExit("port.patch checksum mismatch")
    with tempfile.TemporaryDirectory(prefix="cayley-odd-order-") as temporary:
        staging = Path(temporary)
        for relative, checksums in manifest["files"].items():
            path = Path(relative)
            if path.is_absolute() or ".." in path.parts:
                raise SystemExit("invalid path in source manifest")
            if checksums["upstream_sha256"] is None:
                continue
            original = subprocess.check_output(
                ["git", "-C", str(upstream), "show", revision + ":" + relative]
            )
            if digest(original) != checksums["upstream_sha256"]:
                raise SystemExit(f"upstream checksum mismatch: {relative}")
            target = staging / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(original)
        subprocess.run(["git", "apply", "--check", str(patch)], cwd=staging, check=True)
        subprocess.run(["git", "apply", str(patch)], cwd=staging, check=True)
        for relative, checksums in manifest["files"].items():
            if digest((staging / relative).read_bytes()) != checksums["sha256"]:
                raise SystemExit(f"reconstructed checksum mismatch: {relative}")
            if digest((vendor / relative).read_bytes()) != checksums["sha256"]:
                raise SystemExit(f"vendored checksum mismatch: {relative}")
        shutil.copytree(staging, output)
    print(f"Reconstructed and verified {len(manifest['files'])} source files at {output}")


if __name__ == "__main__":
    main()

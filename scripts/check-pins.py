#!/usr/bin/env python3
"""Check the meta-package's dependency pins.

Modes:

  --locked  (default; offline) Internal consistency: every
            `require <Name> from git "<url>" @ "<sha>"` in
            lakefile.lean must match the corresponding entry in
            lake-manifest.json, and any nested test-project manifest
            (tests/*/lake-manifest.json) that resolves the same
            package must agree. Exits non-zero on mismatch — this is
            the PR-blocking mode.

  --drift   (network) Release-coherence report: compare each pin to
            the upstream default branch HEAD (git ls-remote) and to
            each pinned commit's lean-toolchain. Always exits 0 —
            exact-SHA pins lag upstream by design between releases;
            this mode only reports, for the weekly schedule and the
            manual pre-release check.
"""

import json
import pathlib
import re
import subprocess
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent


def lakefile_pins():
    text = (ROOT / "lakefile.lean").read_text()
    pat = re.compile(
        r'require\s+(\w+)\s+from\s+git\s+"([^"]+)"\s+@\s+"([0-9a-f]{40})"')
    return {m[0]: (m[1], m[2]) for m in pat.findall(text)}


def manifest_revs(path):
    data = json.loads(path.read_text())
    return {p["name"]: p.get("rev") for p in data.get("packages", [])}


def check_locked():
    pins = lakefile_pins()
    if not pins:
        print("check-pins: no pins found in lakefile.lean", file=sys.stderr)
        return 1
    failures = []
    top = manifest_revs(ROOT / "lake-manifest.json")
    for name, (_url, sha) in pins.items():
        got = top.get(name)
        if got != sha:
            failures.append(
                f"lake-manifest.json: {name} resolves {got}, lakefile pins {sha}")
    for nested in sorted(ROOT.glob("tests/*/lake-manifest.json")):
        revs = manifest_revs(nested)
        for name, (_url, sha) in pins.items():
            got = revs.get(name)
            if got is not None and got != sha:
                failures.append(
                    f"{nested.relative_to(ROOT)}: {name} resolves {got}, "
                    f"lakefile pins {sha}")
    if failures:
        print("check-pins: PIN / MANIFEST MISMATCH")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"check-pins: {len(pins)} pins consistent across "
          f"lakefile.lean and all manifests")
    return 0


def check_drift():
    pins = lakefile_pins()
    our_toolchain = (ROOT / "lean-toolchain").read_text().strip()
    print("## Dependency pin drift report\n")
    print("| Package | Pinned | Upstream HEAD | Drift | Toolchain |")
    print("|---|---|---|---|---|")
    for name, (url, sha) in sorted(pins.items()):
        try:
            out = subprocess.run(
                ["git", "ls-remote", url, "HEAD"],
                capture_output=True, text=True, timeout=60, check=True).stdout
            head = out.split()[0] if out.split() else "?"
        except Exception as e:  # report-only mode: never fail
            head = f"unreachable ({e.__class__.__name__})"
        drift = "current" if head == sha else "**behind/diverged**"
        tc = "?"
        if url.startswith("https://github.com/"):
            raw = url.replace("https://github.com/",
                              "https://raw.githubusercontent.com/")
            try:
                with urllib.request.urlopen(
                        f"{raw}/{sha}/lean-toolchain", timeout=30) as r:
                    pinned_tc = r.read().decode().strip()
                tc = "match" if pinned_tc == our_toolchain \
                    else f"**{pinned_tc}**"
            except Exception:
                tc = "unreadable"
        print(f"| {name} | `{sha[:9]}` | `{head[:9]}` | {drift} | {tc} |")
    print(f"\nOur toolchain: `{our_toolchain}`. "
          "Exact-SHA pins lagging upstream between releases is expected; "
          "run the release pin-bump sweep before tagging.")
    return 0


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "--locked"
    sys.exit(check_drift() if mode == "--drift" else check_locked())

#!/usr/bin/env python3
"""Check the SoplexFFI runtime link-args block against lp-backend-soplex-ffi.

The `soplexFFIRuntimeLinkArgs` / sanitizer / `leanLibDirArgs` block is
maintained in two lakefiles: this meta-package's and the one in
https://github.com/leanprover/lp-backend-soplex-ffi. Lake offers no way
to share config-eval-time `Array String` values across packages, so the
copies must be kept in sync by hand; they have drifted before (see
https://github.com/leanprover/lp/issues/166 and
https://github.com/leanprover/lp-backend-soplex-ffi/pull/6).

This script compares the shared definitions

    sanitizerEnabled, sanitizerArgs, leanLibDirArgs,
    soplexFFIRuntimeLinkArgs

between our lakefile.lean and the backend's lakefile.lean at the commit
our lakefile pins, after stripping comments and collapsing whitespace.
Comments may differ (each copy explains its own context); code may not.
`soplexFFIRoot` is intentionally NOT compared: the backend derives its
location from `__dir__` layout detection, the meta-package from its own
`defaultPackagesDir`.

The backend lakefile is fetched from raw.githubusercontent.com at the
exact pinned SHA, so the comparison is deterministic and safe to make
PR-blocking. Pass `--backend-file PATH` to compare against a local
checkout instead (offline / development use).

The long-term fix is for SoplexFFI to carry the platform link arguments
in its own `extern_lib`s so consumers need none of this; see
https://github.com/leanprover/lp-backend-soplex-ffi/issues/1.
"""

import argparse
import pathlib
import re
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent

BACKEND_PACKAGE = "LPBackendSoplexFFI"

SHARED_DEFS = [
    "sanitizerEnabled",
    "sanitizerArgs",
    "leanLibDirArgs",
    "soplexFFIRuntimeLinkArgs",
]

# Column-0 keywords that terminate a top-level `def` body.
TOP_LEVEL = re.compile(
    r"^(def|package|require|import|open|@\[|lean_lib|lean_exe|extern_lib)\b|^@\[")


def strip_comments(text):
    """Remove Lean `--` line comments and (nested) `/- -/` block comments,
    leaving string literals (including `s!"..."` interpolations) intact."""
    out = []
    i, n = 0, len(text)
    in_string = False
    block_depth = 0
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if c == "/" and nxt == "-":
                block_depth += 1
                i += 2
            elif c == "-" and nxt == "/":
                block_depth -= 1
                i += 2
            else:
                if c == "\n":
                    out.append(c)  # keep line structure for def extraction
                i += 1
            continue
        if in_string:
            out.append(c)
            if c == "\\" and nxt:
                out.append(nxt)
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
            continue
        if c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        if c == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        if c == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def extract_defs(text, names):
    """Map name -> normalized body for each top-level `def <name>` found
    in comment-stripped `text`. Normalization collapses all whitespace."""
    stripped = strip_comments(text)
    lines = stripped.split("\n")
    found = {}
    i = 0
    while i < len(lines):
        m = re.match(r"^def\s+(\w+)\b", lines[i])
        if m and m[1] in names:
            body = [lines[i]]
            j = i + 1
            while j < len(lines) and not TOP_LEVEL.match(lines[j]):
                body.append(lines[j])
                j += 1
            found[m[1]] = " ".join(" ".join(body).split())
            i = j
        else:
            i += 1
    return found


def backend_pin():
    text = (ROOT / "lakefile.lean").read_text()
    pat = re.compile(
        r'require\s+' + BACKEND_PACKAGE +
        r'\s+from\s+git\s+"([^"]+)"\s+@\s+"([0-9a-f]{40})"')
    m = pat.search(text)
    if not m:
        sys.exit(f"check-link-args-sync: no {BACKEND_PACKAGE} pin "
                 "found in lakefile.lean")
    return m[1], m[2]


def fetch_backend_lakefile():
    url, sha = backend_pin()
    raw = url.replace("https://github.com/",
                      "https://raw.githubusercontent.com/")
    full = f"{raw}/{sha}/lakefile.lean"
    print(f"check-link-args-sync: fetching {full}")
    with urllib.request.urlopen(full, timeout=60) as r:
        return r.read().decode()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend-file", type=pathlib.Path,
                    help="local backend lakefile.lean (skip network fetch)")
    args = ap.parse_args()

    ours = extract_defs((ROOT / "lakefile.lean").read_text(), SHARED_DEFS)
    backend_text = (args.backend_file.read_text() if args.backend_file
                    else fetch_backend_lakefile())
    theirs = extract_defs(backend_text, SHARED_DEFS)

    failures = []
    for name in SHARED_DEFS:
        a, b = ours.get(name), theirs.get(name)
        if a is None or b is None:
            missing = [w for w, v in [("lp", a), ("backend", b)] if v is None]
            failures.append(f"{name}: missing in {', '.join(missing)}")
        elif a != b:
            failures.append(f"{name}: definitions differ\n"
                            f"    lp:      {a}\n"
                            f"    backend: {b}")
    if failures:
        print("check-link-args-sync: LINK-ARGS BLOCK DRIFT "
              "(see https://github.com/leanprover/lp/issues/166)")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"check-link-args-sync: {len(SHARED_DEFS)} shared defs in sync "
          "with the pinned lp-backend-soplex-ffi lakefile")
    return 0


if __name__ == "__main__":
    sys.exit(main())

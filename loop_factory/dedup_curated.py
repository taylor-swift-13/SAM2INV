#!/usr/bin/env python3
"""Deduplicate structurally similar C loop programs in paired ans/question dirs.

Usage:
    python dedup_curated.py <base_dir> [--threshold 0.85] [--keep-per-group 3] [--dry-run]

<base_dir> must contain ans/ and question/ subdirectories with matching *.c files.

Algorithm:
  1. Normalise each question/*.c by stripping comments, alpha-renaming identifiers,
     and replacing integer literals → N.
  2. Group files whose normalised loop bodies have SequenceMatcher ratio > threshold.
  3. For groups larger than --keep-per-group, keep the K most mutually diverse members
     (greedy max-min distance selection).
  4. Delete duplicates from both ans/ and question/, then renumber 1..N.
"""

import argparse
import difflib
import os
import re
import shutil
import sys
import tempfile


# ---------------------------------------------------------------------------
# Normalisation
# ---------------------------------------------------------------------------

_C_KEYWORDS = frozenset(
    "int unsigned long short char void if else while for do return break "
    "continue switch case default struct typedef enum const static extern "
    "sizeof volatile register signed assert".split()
)


def _normalise(code: str) -> str:
    """Strip comments, rename identifiers, replace constants, collapse whitespace."""
    code = re.sub(r"/\*.*?\*/", "", code, flags=re.DOTALL)
    code = re.sub(r"//.*", "", code)

    # Extract from first while/for loop onward (the interesting part)
    m = re.search(r"(?:while|for)\s*\(.*", code, re.DOTALL)
    if m:
        code = m.group(0)

    code = re.sub(r"\b\d+\b", "N", code)

    tokens = re.findall(r"[A-Za-z_]\w*", code)
    rename = {}
    counter = 0
    skip = _C_KEYWORDS | {"N", "main", "main1"}
    for t in tokens:
        if t not in skip and t not in rename:
            rename[t] = f"v{counter}"
            counter += 1
    for old in sorted(rename, key=len, reverse=True):
        code = re.sub(r"\b" + re.escape(old) + r"\b", rename[old], code)

    return re.sub(r"\s+", " ", code).strip()


# ---------------------------------------------------------------------------
# Grouping
# ---------------------------------------------------------------------------


def _find_groups(files: list[str], bodies: dict[str, str], threshold: float):
    """Return list of groups (each a list of filenames) with similarity > threshold."""
    assigned: set[str] = set()
    groups: list[list[str]] = []

    for i, f1 in enumerate(files):
        if f1 in assigned:
            continue
        group = [f1]
        for f2 in files[i + 1 :]:
            if f2 in assigned:
                continue
            ratio = difflib.SequenceMatcher(None, bodies[f1], bodies[f2]).ratio()
            if ratio > threshold:
                group.append(f2)
                assigned.add(f2)
        if len(group) > 1:
            assigned.add(f1)
            groups.append(group)

    return groups, assigned


def _select_diverse(group: list[str], bodies: dict[str, str], k: int) -> list[str]:
    """Greedy max-min diversity: pick k members maximising mutual dissimilarity."""
    if len(group) <= k:
        return list(group)

    kept = [group[0]]

    while len(kept) < k:
        best_score = -1.0
        best_f = None
        for f in group:
            if f in kept:
                continue
            min_dist = min(
                1 - difflib.SequenceMatcher(None, bodies[k_], bodies[f]).ratio()
                for k_ in kept
            )
            if min_dist > best_score:
                best_score = min_dist
                best_f = f
        kept.append(best_f)

    return kept


# ---------------------------------------------------------------------------
# Renumbering
# ---------------------------------------------------------------------------


def _renumber(directory: str):
    """Rename *.c files to 1.c, 2.c, … preserving sort order by original number."""
    cfiles = sorted(
        [f for f in os.listdir(directory) if f.endswith(".c")],
        key=lambda x: int(x.replace(".c", "")),
    )
    tmpd = tempfile.mkdtemp()
    try:
        for i, f in enumerate(cfiles, 1):
            shutil.move(os.path.join(directory, f), os.path.join(tmpd, f"{i}.c"))
        for f in os.listdir(tmpd):
            shutil.move(os.path.join(tmpd, f), os.path.join(directory, f))
    finally:
        if os.path.isdir(tmpd):
            shutil.rmtree(tmpd, ignore_errors=True)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("base_dir", help="Directory containing ans/ and question/ subdirs")
    ap.add_argument("--threshold", type=float, default=0.85, help="Similarity threshold (default 0.85)")
    ap.add_argument("--keep-per-group", type=int, default=3, help="Max files to keep per similar group (default 3)")
    ap.add_argument("--dry-run", action="store_true", help="Print plan without deleting")
    args = ap.parse_args()

    qdir = os.path.join(args.base_dir, "question")
    adir = os.path.join(args.base_dir, "ans")
    for d in (qdir, adir):
        if not os.path.isdir(d):
            sys.exit(f"Error: {d} not found")

    files = sorted(
        [f for f in os.listdir(qdir) if f.endswith(".c")],
        key=lambda x: int(x.replace(".c", "")),
    )
    print(f"Input: {len(files)} files in question/, {len(os.listdir(adir))} in ans/")

    # Normalise
    bodies = {}
    for f in files:
        bodies[f] = _normalise(open(os.path.join(qdir, f)).read())

    # Group
    groups, assigned = _find_groups(files, bodies, args.threshold)

    # Decide what to keep / remove
    to_keep: set[str] = {f for f in files if f not in assigned}  # singletons
    to_remove: set[str] = set()

    for group in groups:
        kept = _select_diverse(group, bodies, args.keep_per_group)
        to_keep.update(kept)
        to_remove.update(f for f in group if f not in kept)

    # Report
    print(f"\nFound {len(groups)} similar groups:")
    for g in groups:
        kept = [f for f in g if f in to_keep]
        removed = len(g) - len(kept)
        print(f"  ({len(g):2d} files) keep {kept}, remove {removed}")
    print(f"\nTotal: keeping {len(to_keep)}, removing {len(to_remove)}")

    if args.dry_run:
        print("\n[dry-run] No files deleted.")
        return

    # Delete
    for f in to_remove:
        for d in (qdir, adir):
            p = os.path.join(d, f)
            if os.path.exists(p):
                os.remove(p)

    # Renumber
    _renumber(qdir)
    _renumber(adir)

    final_q = sorted(os.listdir(qdir), key=lambda x: int(x.replace(".c", "")))
    final_a = sorted(os.listdir(adir), key=lambda x: int(x.replace(".c", "")))
    print(f"Final: {len(final_q)} in question/ (1.c..{final_q[-1]}), {len(final_a)} in ans/ (1.c..{final_a[-1]})")


if __name__ == "__main__":
    main()

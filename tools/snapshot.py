#!/usr/bin/env python3
"""Capture one observation of openai/ten-proofs.

Two modes:

  seed   - compute rows from git tags already in this archive (offline, exact)
  poll   - ask GitHub for the current head; if it is new, fetch + tag it,
           then record a row

Every row is appended to snapshots.tsv and a full record is written to
snapshots/<sha>.json. The archive's own git history is the changelog that
upstream does not keep.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
UPSTREAM = "openai/ten-proofs"
TSV = os.path.join(ROOT, "snapshots.tsv")
SNAPDIR = os.path.join(ROOT, "snapshots")

COLUMNS = [
    "observed_utc", "committed_utc", "sha", "parents", "message", "author",
    "blobs", "lean_files", "lean_bytes", "total_bytes",
    "nanoda_on", "nanoda_off", "axioms_ok", "lakefile_roots", "challenge_files",
    "stars", "forks",
]

CHALLENGE_KEYS = [
    "A_SpherePacking", "B_BinaryCodes", "B_SphericalCodes",
    "C_PermanentFormulaLowerBound", "D_NonSoficGroup", "E_ConnesRigidity",
    "F_EhrhartVolumeInequality", "G_QuantumParallelRepetition", "H_GapCVP",
    "I_MulticolorTriangleRamsey", "J_CompactnessConjecture", "J_TwoDegenerateGraphs",
]
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def git(*args: str) -> str:
    out = subprocess.run(["git", "-C", ROOT, *args], capture_output=True, check=True)
    return out.stdout.decode("utf-8", "replace")


def gh_json(path: str):
    out = subprocess.run(["gh", "api", path], capture_output=True)
    if out.returncode != 0:
        return None
    return json.loads(out.stdout.decode("utf-8", "replace"))


def tree_shape(sha: str) -> dict:
    """Blob counts and byte totals for a commit, straight from the object store."""
    blobs = lean = lean_bytes = total = 0
    for line in git("ls-tree", "-r", "--long", sha).splitlines():
        if not line.strip():
            continue
        meta, path = line.split("\t", 1)
        size = meta.split()[3]
        if size == "-":
            continue
        size = int(size)
        blobs += 1
        total += size
        if path.endswith(".lean"):
            lean += 1
            lean_bytes += size
    return {"blobs": blobs, "lean_files": lean, "lean_bytes": lean_bytes,
            "total_bytes": total}


def read_at(sha: str, path: str):
    try:
        return git("show", f"{sha}:{path}")
    except subprocess.CalledProcessError:
        return None


def integrity(sha: str) -> dict:
    """The three things worth watching: nanoda coverage, axiom allowlists,
    and whether the declared lakefile roots actually exist."""
    on, off, axioms_ok = [], [], True
    per = {}
    for key in CHALLENGE_KEYS:
        raw = read_at(sha, f"ComparatorChallenges/{key}.json")
        if raw is None:
            continue
        try:
            doc = json.loads(raw)
        except json.JSONDecodeError:
            continue
        nanoda = bool(doc.get("enable_nanoda"))
        ax = set(doc.get("permitted_axioms") or [])
        (on if nanoda else off).append(key)
        if ax != STANDARD_AXIOMS:
            axioms_ok = False
        per[key] = {"enable_nanoda": nanoda, "permitted_axioms": sorted(ax)}

    lake = read_at(sha, "lakefile.toml") or ""
    roots = [ln.split('"')[1] for ln in lake.splitlines()
             if ln.strip().startswith('"ComparatorChallenges.')]
    present = [p for p in git("ls-tree", "-r", "--name-only", sha).splitlines()
               if p.startswith("ComparatorChallenges/") and p.endswith(".lean")]
    missing = sorted({r.split(".", 1)[1] for r in roots}
                     - {os.path.basename(p)[:-5] for p in present})

    return {"nanoda_on": len(on), "nanoda_off": len(off), "nanoda_off_names": off,
            "axioms_ok": axioms_ok, "lakefile_roots": len(roots),
            "challenge_files": len(present), "missing_roots": missing,
            "challenges": per}


def record(sha: str, observed: str, stars=None, forks=None) -> dict:
    body = git("show", "-s", "--format=%ct%n%P%n%s%n%an <%ae>", sha).splitlines()
    ts, parents, message, author = (body + ["", "", "", ""])[:4]
    committed = datetime.fromtimestamp(int(ts), timezone.utc).isoformat(
        timespec="seconds").replace("+00:00", "Z")
    row = {"observed_utc": observed, "committed_utc": committed, "sha": sha,
           "parents": parents.strip() or "(none - root commit)",
           "message": message, "author": author,
           "stars": stars if stars is not None else "",
           "forks": forks if forks is not None else ""}
    row.update(tree_shape(sha))
    row.update(integrity(sha))
    return row


def write(rows: list) -> None:
    os.makedirs(SNAPDIR, exist_ok=True)
    for r in rows:
        path = os.path.join(SNAPDIR, r["sha"][:12] + ".json")
        with open(path, "w", encoding="utf-8", newline="\n") as fh:
            json.dump(r, fh, indent=2, sort_keys=True)
            fh.write("\n")

    existing, seen = [], set()
    if os.path.exists(TSV):
        with open(TSV, encoding="utf-8") as fh:
            lines = fh.read().splitlines()
        for ln in lines[1:]:
            if ln.strip():
                existing.append(ln)
                seen.add(ln.split("\t")[2])

    for r in rows:
        if r["sha"] in seen:
            continue
        existing.append("\t".join(str(r.get(c, "")) for c in COLUMNS))
        seen.add(r["sha"])

    existing.sort(key=lambda ln: ln.split("\t")[1])
    with open(TSV, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\t".join(COLUMNS) + "\n")
        fh.write("\n".join(existing) + "\n")


def cmd_seed() -> int:
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    rows = []
    for tag in sorted(git("tag", "-l", "snapshot-*").split()):
        sha = git("rev-parse", tag).strip()
        rows.append(record(sha, now))
        print("  seeded {:<28} {}".format(tag, sha[:12]))
    write(rows)
    return 0


def cmd_poll() -> int:
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    head = gh_json("repos/" + UPSTREAM + "/commits/main")
    if not head:
        print("could not reach upstream", file=sys.stderr)
        return 1
    sha = head["sha"]
    meta = gh_json("repos/" + UPSTREAM) or {}

    known = {git("rev-parse", t).strip()
             for t in git("tag", "-l", "snapshot-*").split()}
    if sha in known:
        print("unchanged: " + sha[:12])
        return 0

    n = len(known)
    print("NEW HEAD " + sha[:12] + " - fetching")
    subprocess.run(["git", "-C", ROOT, "fetch", "--no-tags",
                    "https://github.com/" + UPSTREAM + ".git", sha], check=True)
    tag = "snapshot-{:02d}-{}".format(n, sha[:9])
    subprocess.run(["git", "-C", ROOT, "tag", "-f", tag, sha], check=True)
    write([record(sha, now, meta.get("stargazers_count"), meta.get("forks_count"))])
    print("tagged " + tag)
    return 0


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "poll"
    sys.exit(cmd_seed() if mode == "seed" else cmd_poll())

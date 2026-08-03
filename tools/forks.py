"""Recover upstream states that were never observed directly, from forks.

Why this exists
---------------
Polling only sees the states that happen to be HEAD when a poll fires. Between
2026-08-01T10:25Z and 18:08Z the poller recorded nothing, and that window looked
like a quiet period. It was not: five separate upstream states landed in it, and
every one of them survived only because somebody had forked the repository while
it was HEAD.

A GitHub fork keeps its own ref pointing at whatever it forked, so the fork
network is a distributed, uncoordinated archive of states upstream has since
discarded. Sweeping it recovered five states and, with them, the fact that
upstream briefly kept a real commit history.

Method
------
1. List every fork of the upstream repository.
2. `git ls-remote` each one to collect *all* refs, not just HEAD -- branches
   people pushed can be built on states main no longer has.
3. Fetch each distinct SHA by its **full 40 characters**. Abbreviated SHAs are
   rejected by the git wire protocol, which fails in a way that looks like the
   object is missing rather than like a bad request.
4. Walk each fetched commit's ancestry and keep the commits whose author matches
   upstream. Third-party commits sit on top of upstream states, so the ancestry
   is where the recovered states actually are.
5. Tag anything new so it can never be lost again.

Usage
-----
    python tools/forks.py            # report only
    python tools/forks.py --tag      # also create snapshot-r*-<sha> tags
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
UPSTREAM = "openai/ten-proofs"
UPSTREAM_AUTHOR = "Boris Alexeev"
TAG_PREFIX = "snapshot-r"


def git(*args: str, check: bool = False) -> str:
    proc = subprocess.run(["git", "-C", str(ROOT), *args],
                          capture_output=True, text=True)
    if check and proc.returncode != 0:
        raise SystemExit("git {} failed: {}".format(" ".join(args), proc.stderr.strip()))
    return proc.stdout


def gh_json(path: str):
    proc = subprocess.run(["gh", "api", "--paginate", path],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit("gh api {} failed: {}".format(path, proc.stderr.strip()))
    # --paginate concatenates JSON arrays; normalise to one list.
    text = proc.stdout.strip().replace("][", ",")
    return json.loads(text) if text else []


def known_shas() -> set[str]:
    out = set()
    for tag in git("tag", "-l", "snapshot-*").split():
        sha = git("rev-list", "-n", "1", tag).strip()
        if sha:
            out.add(sha)
    return out


def fork_refs() -> dict[str, str]:
    """Every distinct SHA reachable from any ref of any fork -> where it was seen."""
    seen: dict[str, str] = {}
    forks = [f["full_name"] for f in gh_json("repos/{}/forks".format(UPSTREAM))]
    print("forks: {}".format(len(forks)))
    for name in forks:
        proc = subprocess.run(["git", "ls-remote", "https://github.com/{}.git".format(name)],
                              capture_output=True, text=True)
        if proc.returncode != 0:
            print("  unreachable: {}".format(name))
            continue
        for line in proc.stdout.splitlines():
            parts = line.split("\t")
            if len(parts) == 2 and len(parts[0]) == 40:
                seen.setdefault(parts[0], "{} {}".format(name, parts[1]))
    print("distinct SHAs across all fork refs: {}".format(len(seen)))
    return seen


def fetch(sha: str, origin: str) -> bool:
    """Fetch one object by full SHA. Abbreviated SHAs do not work here."""
    repo = origin.split()[0]
    proc = subprocess.run(
        ["git", "-C", str(ROOT), "fetch", "-q",
         "https://github.com/{}.git".format(repo), sha],
        capture_output=True, text=True)
    return proc.returncode == 0 and git("cat-file", "-t", sha).strip() == "commit"


def upstream_commits(head: str) -> list[dict]:
    """Upstream-authored commits reachable from head, oldest first."""
    fmt = "%H%x1f%an%x1f%cI%x1f%p%x1f%s"
    out = []
    for line in git("log", "--format=" + fmt, head).splitlines():
        sha, author, when, parents, subject = line.split("\x1f")
        if author != UPSTREAM_AUTHOR:
            continue
        stamp = dt.datetime.fromisoformat(when).astimezone(dt.timezone.utc)
        out.append({"sha": sha, "utc": stamp, "parents": parents.split(),
                    "subject": subject})
    return sorted(out, key=lambda c: c["utc"])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tag", action="store_true", help="tag newly recovered states")
    args = ap.parse_args()

    known = known_shas()
    print("states already archived: {}".format(len(known)))

    found: dict[str, dict] = {}
    for sha, origin in fork_refs().items():
        if sha in known:
            continue
        if not fetch(sha, origin):
            print("  could not fetch {} from {}".format(sha[:9], origin))
            continue
        for commit in upstream_commits(sha):
            if commit["sha"] not in known:
                commit["origin"] = origin
                found.setdefault(commit["sha"], commit)

    if not found:
        print("\nno unrecorded upstream states found")
        return 0

    print("\nrecovered {} upstream state(s) not previously archived:".format(len(found)))
    ordered = sorted(found.values(), key=lambda c: c["utc"])
    for c in ordered:
        print("  {}  {}  parents={}  {!r}  via {}".format(
            c["utc"].strftime("%Y-%m-%dT%H:%M:%SZ"), c["sha"][:9],
            len(c["parents"]), c["subject"], c["origin"]))

    parented = [c for c in ordered if c["parents"]]
    if parented:
        print("\n{} recovered state(s) have a parent -- upstream kept a real "
              "history at least briefly:".format(len(parented)))
        for c in parented:
            print("  {} -> {}  {!r}".format(
                c["parents"][0][:9], c["sha"][:9], c["subject"]))

    if args.tag:
        for i, c in enumerate(ordered, 1):
            tag = "{}{}-{}".format(TAG_PREFIX, i, c["sha"][:9])
            git("tag", "-f", tag, c["sha"], check=True)
            print("tagged {}".format(tag))
        print("\nrun `python tools/claims.py` and push tags to publish")
    else:
        print("\nrerun with --tag to archive these")
    return 0


if __name__ == "__main__":
    sys.exit(main())

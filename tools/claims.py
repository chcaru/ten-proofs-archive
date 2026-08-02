"""Compare what the artifact CLAIMS across every preserved state.

snapshot.py records the shape of each state. This records its content: the set
of theorems each state declares it proves, whether those declarations resolve,
and how much of the surrounding text moved.

The distinction this tool exists to draw is between two very different things:

  * a proof being rewritten  -- normal, healthy, uninteresting
  * a claim being changed    -- the goalposts moving, with no changelog

Only an archive can tell them apart, because upstream keeps no history.

    python tools/claims.py            # write claims.tsv + claim-churn.md
    python tools/claims.py --print    # also dump to stdout
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

CHALLENGE_DIR = "ComparatorChallenges"
CLAIMS_TSV = ROOT / "claims.tsv"
CHURN_MD = ROOT / "claim-churn.md"


def git(*args: str) -> str | None:
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True)
    return None if r.returncode else r.stdout.decode("utf-8", "replace")


def ordered_tags() -> list[tuple[str, int, str]]:
    """(tag, upstream commit time, sha) for every snapshot, oldest first."""
    out = []
    for tag in (git("tag", "-l", "snapshot-*") or "").split():
        sha = (git("rev-parse", tag) or "").strip()
        ts = int((git("show", "-s", "--format=%ct", sha) or "0").strip())
        out.append((tag, ts, sha))
    out.sort(key=lambda r: r[1])
    return out


def challenges(tag: str) -> list[str]:
    listing = git("ls-tree", "--name-only", "{}:{}".format(tag, CHALLENGE_DIR)) or ""
    return sorted(n[:-5] for n in listing.split() if n.endswith(".json"))


_bodies: dict[str, str] = {}


def body(ref: str) -> str:
    if ref not in _bodies:
        _bodies[ref] = git("show", ref) or ""
    return _bodies[ref]


def binds(tag: str, leaf: str) -> bool:
    """Is `leaf` bound by a theorem/lemma anywhere in this state's tree?

    Lean wraps long declarations, so the keyword and the name are often on
    separate lines. git grep is line-oriented and cannot see that; narrow to
    candidate files with a fixed-string grep, then match multiline in Python.
    """
    r = subprocess.run(
        ["git", "-C", str(ROOT), "grep", "-l", "-F", leaf, tag, "--", "*.lean"],
        capture_output=True)
    if not r.stdout.strip():
        return False
    pat = re.compile(
        r"(?:^|\n)\s*(?:@\[[^\]]*\]\s*)?"
        r"(?:private\s+|protected\s+|nonrec\s+)*"
        r"(?:theorem|lemma)\s+" + re.escape(leaf) + r"\b")
    return any(pat.search(body(ref.strip()))
               for ref in r.stdout.decode("utf-8", "replace").splitlines()
               if ref.strip())


def read_state(tag: str) -> dict:
    st = {"challenges": challenges(tag), "names": {}, "stmt": {}, "sol": {},
          "sorry_stmt": 0, "sorry_sol": 0, "axioms": set(), "unresolved": []}
    seen_sol = set()
    for key in st["challenges"]:
        raw = git("show", "{}:{}/{}.json".format(tag, CHALLENGE_DIR, key))
        if not raw:
            continue
        doc = json.loads(raw)
        st["names"][key] = set(doc.get("theorem_names") or ())
        st["axioms"] |= set(doc.get("permitted_axioms") or ())

        stmt_ref = "{}:{}/{}.lean".format(tag, CHALLENGE_DIR, key)
        st["stmt"][key] = (git("rev-parse", stmt_ref) or "?").strip()[:12]
        st["sorry_stmt"] += body(stmt_ref).count("sorry")

        mod = doc.get("solution_module")
        sol_ref = "{}:{}.lean".format(tag, mod)
        st["sol"][key] = (git("rev-parse", sol_ref) or "-").strip()[:12]
        if mod not in seen_sol:
            seen_sol.add(mod)
            st["sorry_sol"] += body(sol_ref).count("sorry")

        for name in st["names"][key]:
            if not binds(tag, name.split(".")[-1]):
                st["unresolved"].append("{}::{}".format(key, name))
    return st


def main() -> int:
    tags = ordered_tags()
    if not tags:
        print("no snapshot-* tags found", file=sys.stderr)
        return 1

    states = [(tag, ts, sha, read_state(tag)) for tag, ts, sha in tags]

    rows = ["\t".join([
        "tag", "sha", "committed_utc", "challenges", "declared_theorems",
        "unresolved", "statement_files_distinct_so_far", "sorry_statements",
        "sorry_solutions", "axioms"])]
    seen_stmt: dict[str, set[str]] = {}
    for tag, ts, sha, st in states:
        for key, blob in st["stmt"].items():
            seen_stmt.setdefault(key, set()).add(blob)
        rows.append("\t".join([
            tag, sha[:12],
            subprocess.run(["git", "-C", str(ROOT), "show", "-s",
                            "--format=%cd", "--date=format-local:%Y-%m-%dT%H:%M:%SZ",
                            sha], capture_output=True,
                           env={"TZ": "UTC", **__import__("os").environ}
                           ).stdout.decode().strip(),
            str(len(st["challenges"])),
            str(sum(len(v) for v in st["names"].values())),
            str(len(st["unresolved"])) if st["unresolved"] else "0",
            str(sum(len(v) for v in seen_stmt.values())),
            str(st["sorry_stmt"]), str(st["sorry_sol"]),
            ",".join(sorted(st["axioms"]))]))
    CLAIMS_TSV.write_text("\n".join(rows) + "\n", encoding="utf-8")

    lines = [
        "# What the artifact claimed, state by state",
        "",
        "Generated by `tools/claims.py` from the preserved tags. Upstream keeps",
        "no history, so this comparison does not exist anywhere else.",
        "",
        "A changed *proof* is unremarkable. A changed *claim* is not. This file",
        "separates the two.",
        "",
        "## Declared theorems",
        "",
    ]
    prev = None
    for tag, ts, sha, st in states:
        total = sum(len(v) for v in st["names"].values())
        label = tag.replace("snapshot-", "")
        if prev is None:
            lines.append("- **{}** -- {} declared theorems (baseline)".format(label, total))
        else:
            adds, dels = [], []
            for key in sorted(set(st["names"]) | set(prev["names"])):
                cur_n = st["names"].get(key, set())
                old_n = prev["names"].get(key, set())
                adds += [(key, n) for n in sorted(cur_n - old_n)]
                dels += [(key, n) for n in sorted(old_n - cur_n)]
            delta = total - sum(len(v) for v in prev["names"].values())
            if not adds and not dels:
                lines.append("- **{}** -- {} declared theorems (no change)".format(label, total))
            else:
                lines.append("- **{}** -- {} declared theorems ({:+d}) **claims changed**"
                             .format(label, total, delta))
                for key, n in adds:
                    lines.append("    - added: `{}` &rarr; `{}`".format(key, n))
                for key, n in dels:
                    lines.append("    - removed: `{}` &rarr; `{}`".format(key, n))
        prev = st

    first, last = states[0][3], states[-1][3]
    gone, new = [], []
    for key in sorted(set(first["names"]) | set(last["names"])):
        gone += [(key, n) for n in sorted(first["names"].get(key, set())
                                          - last["names"].get(key, set()))]
        new += [(key, n) for n in sorted(last["names"].get(key, set())
                                         - first["names"].get(key, set()))]
    lines += ["", "## Released state vs newest state", "",
              "- declared at release, absent now: **{}**".format(len(gone))]
    lines += ["    - `{}` &rarr; `{}`".format(k, n) for k, n in gone]
    lines += ["- absent at release, declared now: **{}**".format(len(new))]
    lines += ["    - `{}` &rarr; `{}`".format(k, n) for k, n in new]

    lines += ["", "## How often each file was rewritten", "",
              "| challenge | statement versions | solution versions |",
              "| --- | ---: | ---: |"]
    for key in sorted(seen_stmt):
        sols = {st["sol"].get(key) for _, _, _, st in states if key in st["sol"]}
        lines.append("| `{}` | {} | {} |".format(key, len(seen_stmt[key]), len(sols)))

    lines += ["", "## What never moved", ""]
    ax = {",".join(sorted(st["axioms"])) for _, _, _, st in states}
    unresolved = sum(len(st["unresolved"]) for _, _, _, st in states)
    sol_sorry = {st["sorry_sol"] for _, _, _, st in states}
    lines += [
        "- permitted axioms: **{}** across every state and challenge (`{}`)".format(
            "unchanged" if len(ax) == 1 else "CHANGED", next(iter(ax))),
        "- declared theorems missing from the tree: **{}**, at any state".format(unresolved),
        "- `sorry` in solution modules: **{}** at every state".format(
            next(iter(sol_sorry)) if len(sol_sorry) == 1 else sorted(sol_sorry)),
    ]
    CHURN_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print("wrote {} ({} states)".format(CLAIMS_TSV.name, len(states)))
    print("wrote {}".format(CHURN_MD.name))
    if "--print" in sys.argv:
        print()
        print(CHURN_MD.read_text(encoding="utf-8"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

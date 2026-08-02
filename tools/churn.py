"""Is upstream converging, or still moving?

Bytes and files changed between consecutive states, plus the interval between
them. If churn and frequency are both falling, the artifact is settling and the
notebook can quote a state with reasonable confidence. If not, anything written
about it is provisional.
"""
import subprocess
from datetime import datetime, timezone

ROOT = r"C:\dev\ten-proofs-archive"


def git(*a):
    r = subprocess.run(["git", "-C", ROOT, *a], capture_output=True)
    return None if r.returncode else r.stdout.decode("utf-8", "replace")


order = []
for t in (git("tag", "-l", "snapshot-*") or "").split():
    sha = (git("rev-parse", t) or "").strip()
    ts = int((git("show", "-s", "--format=%ct", sha) or "0").strip())
    order.append((ts, t, sha))
order.sort()

print("{:<22} {:>10} {:>9} {:>10} {:>12}".format(
    "state", "gap", "files", "insertions", "deletions"))
print("-" * 68)
prev = None
for ts, tag, sha in order:
    label = tag.replace("snapshot-", "")
    when = datetime.fromtimestamp(ts, timezone.utc)
    if prev is None:
        print("{:<22} {:>10} {:>9} {:>10} {:>12}".format(
            label, "-", "-", "-", "-"))
    else:
        gap = (ts - prev[0]) / 60.0
        stat = git("diff", "--shortstat", prev[1], tag) or ""
        nums = [int(x) for x in __import__("re").findall(r"(\d+)", stat)]
        files = nums[0] if len(nums) > 0 else 0
        ins = nums[1] if len(nums) > 1 else 0
        dele = nums[2] if len(nums) > 2 else 0
        print("{:<22} {:>9.0f}m {:>9,} {:>10,} {:>12,}".format(
            label, gap, files, ins, dele))
    prev = (ts, tag)

last_ts = order[-1][0]
now = datetime.now(timezone.utc).timestamp()
quiet = (now - last_ts) / 3600.0
gaps = [(order[i][0] - order[i - 1][0]) / 3600.0 for i in range(1, len(order))]
print()
print("last observed change : {} UTC".format(
    datetime.fromtimestamp(last_ts, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")))
print("quiet for            : {:.1f} hours".format(quiet))
print("longest prior gap    : {:.1f} hours".format(max(gaps)))
print("verdict              : {}".format(
    "quiet period now EXCEEDS every observed gap -- plausibly settled"
    if quiet > max(gaps) else
    "still inside the range of normal upstream gaps -- do not call it settled"))

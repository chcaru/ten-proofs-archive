# ten-proofs-archive

A preservation archive and change log for
[`openai/ten-proofs`](https://github.com/openai/ten-proofs), the Lean
formalization artifact released with OpenAI's *Ten advances in mathematics and
theoretical computer science* (2026-08-01).

This repository exists because **upstream keeps no history of its own.**

## Why

Every state `openai/ten-proofs` has ever been observed in is a **parentless root
commit with the commit message `.`**. Not one of them has a parent. Each push
replaces the entire repository, so the previous state becomes unreachable from
any ref and is eventually garbage-collected. There are no tags, no releases and
no changelog.

Seven distinct states were captured on the day of release, six of them within
twelve hours. The artifact changed **six times after the version people first
read**, including changes to the proof files themselves.

This archive pins each of those states to a permanent tag so they remain
verifiable after upstream drops them.

## What is here

| Path | Contents |
| --- | --- |
| `snapshot-*` tags | The full tree of every observed upstream state |
| `snapshots.tsv` | One row per state: shape, verification settings, build integrity |
| `snapshots/<sha>.json` | The full record for a state, including per-challenge settings |
| `poll-log.tsv` | One row per observation, including observations that saw no change |
| `tools/snapshot.py` | `seed` (recompute from tags) and `poll` (capture a new head) |
| `.github/workflows/track.yml` | Hourly poll; preserves any new head automatically |

The `poll-log.tsv` heartbeat is intentional. Recording only changes cannot
distinguish *"upstream was stable"* from *"nobody was watching"*, and that
distinction is the whole point of the archive.

## The observed record

Times are UTC on 2026-08-01. The repository was created at 06:10:06.

| Committed | SHA | Blobs | `.lean` | `.lean` bytes | nanoda | Note |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| 07:42:26 | `66af8383b` | 6,129 | 4,319 | 210,723,976 | 10 / 12 | The version most readers saw. Survives **only** in third-party forks |
| 08:42:25 | `a13547c6b` | 6,130 | 4,319 | 210,693,429 | 10 / 12 | 2,552 files changed, 68,398 lines deleted |
| 10:02:08 | `e62211d28` | 43 | 23 | 20,952,180 | **9 / 12** | The collapse. Also the low point for verification coverage |
| 10:20:42 | `a1f2a5481` | 43 | 23 | 20,950,627 | 10 / 12 | |
| 10:22:00 | `cca357b19` | 43 | 23 | 20,950,627 | 10 / 12 | |
| 10:25:18 | `bfa69a496` | 43 | 23 | 20,950,627 | 10 / 12 | |
| 18:08:14 | `d0e1ae7de` | 43 | 23 | 21,638,952 | **12 / 12** | Same shape, 20 of 43 files rewritten |

### What the data shows

**The artifact shrank by 99.3%.** From 4,319 `.lean` files and 201 MB to 23 files
and 20 MB. Most of the original bulk was `ConnesRigidity/`: 6,087 machine-generated
files, 336.8 MB, **99.4% of the entire release**, reached through a 30-byte shim.

**Verification coverage moved in both directions.** Each of the twelve Comparator
challenges declares whether it is re-checked by `nanoda`, an independent Lean
kernel implementation. Coverage went **10 → 10 → 9 → 10 → 10 → 10 → 12**. The
10:02 push briefly dropped `E_ConnesRigidity`; the final push closed the
long-standing gap on `G_QuantumParallelRepetition` and `H_GapCVP`. None of this
was announced.

**The axiom allowlists never moved.** All twelve challenges pin exactly
`propext`, `Quot.sound` and `Classical.choice` in every observed state. `sorryAx`
and `Lean.ofReduceBool` are excluded throughout, which means a proof leaning on
`sorry` or `native_decide` fails the harness mechanically. This is the strongest
and most stable property of the artifact.

**One build defect has survived every rewrite.** `lakefile.toml` has declared 13
`ComparatorChallenges` roots against 12 present files in all seven states;
`C_PermanentSuperquadraticStandalone` has never existed. Separately, a stranger
fixed a different build error at 08:35 — before upstream did.

**The last change was not repackaging.** The 18:08 push kept the file list
identical while rewriting 20 of 43 files: `MetricCodes.lean` +49%,
`ConnesRigidity.lean` −29%, `formalization.yaml` +155%. The formal content of a
published mathematical result changed after publication, with no record.

## Reproducing any claim

```bash
git clone https://github.com/<owner>/ten-proofs-archive
cd ten-proofs-archive
git checkout snapshot-01-released-fork   # the version readers actually saw
python3 tools/snapshot.py seed           # recompute every row from the objects
```

## Scope and intent

This is a preservation and measurement record, not an accusation. Two of the
observed changes made the artifact **better**, and the mathematics is not in
question here. The point is narrower and entirely checkable: a released
mathematical artifact changed seven times without a changelog, and nothing in
the publishing apparatus recorded that it had. A reader who cites the 07:00
version and a reader who cites the 19:00 version cite different mathematics
under the same URL.

Upstream content belongs to its authors and is preserved here under its original
license for verification purposes.

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

**Nine distinct states** have been captured so far, all within twenty hours of
release. The artifact changed **eight times after the version people first
read**, including repeated changes to the proof files themselves.

This archive pins each of those states to a permanent tag so they remain
verifiable after upstream drops them.

## What is here

| Path | Contents |
| --- | --- |
| `snapshot-*` tags | The full tree of every observed upstream state |
| `snapshots.tsv` | One row per state: shape, verification settings, build integrity |
| `snapshots/<sha>.json` | The full record for a state, including per-challenge settings |
| `poll-log.tsv` | One row per observation, including observations that saw no change |
| `claims.tsv` | One row per state: declared theorems, unresolved claims, `sorry` counts, axioms |
| `claim-churn.md` | Every theorem added to or removed from a challenge, with dates |
| `tools/snapshot.py` | `seed` (recompute from tags) and `poll` (capture a new head) |
| `tools/claims.py` | Regenerates `claims.tsv` and `claim-churn.md` from the tags |
| `.github/workflows/track.yml` | Polls every 5 minutes in a loop; preserves any new head automatically |

The `poll-log.tsv` heartbeat is intentional. Recording only changes cannot
distinguish *"upstream was stable"* from *"nobody was watching"*, and that
distinction is the whole point of the archive.

## The observed record

Times are UTC on 2026-08-01. The repository was created at 06:10:06.

Times are UTC. 07:42 through 18:08 are 2026-08-01; the last row is 2026-08-02.

| Committed | SHA | Blobs | `.lean` | `.lean` bytes | nanoda | Build | Note |
| --- | --- | ---: | ---: | ---: | ---: | :---: | --- |
| 07:42:26 | `66af8383b` | 6,129 | 4,319 | 210,723,976 | 10 / 12 | broken | The version most readers saw. Survived **only** in third-party forks |
| 08:42:25 | `a13547c6b` | 6,130 | 4,319 | 210,693,429 | 10 / 12 | broken | 2,552 files changed, 68,398 lines deleted. **Never appeared in the event feed** |
| 10:02:08 | `e62211d28` | 43 | 23 | 20,952,180 | **9 / 12** | broken | The collapse. Also the low point for verification coverage |
| 10:20:42 | `a1f2a5481` | 43 | 23 | 20,950,627 | 10 / 12 | broken | |
| 10:22:00 | `cca357b19` | 43 | 23 | 20,950,627 | 10 / 12 | broken | |
| 10:25:18 | `bfa69a496` | 43 | 23 | 20,950,627 | 10 / 12 | broken | |
| ★ 11:21:53 | `aae1395c9` | 43 | 23 | 20,950,627 | **12 / 12** | broken | Three-line push: both `enable_nanoda` flags on, and `formalization.yaml` renamed to the public title |
| ★ 11:46:12 | `6060af02c` | 43 | 23 | 20,369,623 | 12 / 12 | broken | **The only state with a parent.** Message: *"Remove unused Connes rigidity proof declarations"* — 14,989 deletions, no claim changed |
| ★ 12:29:41 | `706c3c30a` | 43 | 23 | 20,369,623 | 12 / 12 | broken | Root commit again; the 24-minute history ends here |
| ★ 15:57:46 | `0166452d0` | 43 | 23 | 18,108,692 | 12 / 12 | broken | Last state declaring 41 theorems |
| ★ 17:11:14 | `5a102c122` | 43 | 23 | 20,699,786 | 12 / 12 | broken | Declared theorems 41 → **38**, and `sorry` 45 → **42**, together |
| 18:08:14 | `d0e1ae7de` | 43 | 23 | 21,638,952 | 12 / 12 | broken | Same shape, 20 of 43 files rewritten |
| 23:29:17 | `39fba5b07` | 43 | 23 | 21,638,952 | 12 / 12 | **fixed** | Dangling lakefile root removed; a stale `formalization.yaml` path corrected |
| 00:22:31 | `94bc0feb6` | 43 | 23 | 21,638,888 | 12 / 12 | fixed | `MetricCodes.lean` edited again |

**★ = recovered from third-party forks, not from polling.** Run `python tools/forks.py` to repeat
the sweep; add `--tag` to record anything new. The method: enumerate every fork, `git ls-remote`
**all refs** (not just the default branch — third-party working branches sit on old upstream
states), fetch each distinct SHA by its **full 40 characters** (abbreviated SHAs fail over the git
wire protocol), walk each commit's ancestry, and keep those authored upstream.

**This archive's own polling missed five of fourteen states.** A poller only sees what is on the
branch at the moment it looks; five states lived and were replaced between looks. They exist here
only because other people had independently forked the repository during those windows.

> **As of 2026-08-02, GitHub shows no public evidence that this repository was ever rewritten.**
> `repos/openai/ten-proofs/events` returns 30 events, all `ForkEvent`/`WatchEvent` and **zero
> `PushEvent`**; `git ls-remote` returns one ref, no tags, no branches. From first rewrite to the
> total disappearance of the public record: about **25 hours**.

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

**A build defect stood for seventeen hours, then was silently fixed.**
`lakefile.toml` declared 13 `ComparatorChallenges` roots against 12 present
files in the first seven states; `C_PermanentSuperquadraticStandalone` never
existed. It was removed at 23:29, along with a `formalization.yaml` entry still
pointing at `MetricCodes/Base.lean`, a path that stopped existing at the 10:02
collapse. Separately, a stranger fixed a different build error at 08:35 — before
upstream did. Any claim about this artifact's build integrity is only true of a
specific timestamp.

**Changes to the proofs continued after the shape settled.** The 18:08 push kept
the file list identical while rewriting 20 of 43 files: `MetricCodes.lean` +49%,
`ConnesRigidity.lean` −29%, `formalization.yaml` +155%. The 00:22 push edited
`MetricCodes.lean` again. The formal content of a published mathematical result
kept changing after publication, with no record.

**What this archive cannot do.** A poll cannot catch a state that exists for less
than one poll interval, and upstream once produced four distinct
states in 23 minutes. States between 06:10:06 and 07:42:26 that nobody forked
are gone permanently. **Nine is a floor, not a count** — and `poll-log.tsv`
exists so that the difference between "stable" and "unobserved" stays visible.

**And the archive had to take its own advice about that.** The workflow was
originally written with a `*/15` cron and described as polling every 15
minutes. It did not. Measured from `poll-log.tsv`, the observed interval was
**min 29 / median 61 / max 82 minutes**, followed by a 129-minute gap: GitHub
throttles scheduled workflows on low-activity repositories and may skip them
entirely. A configured cadence is not an observed one, which is the same
mistake this archive exists to make visible — so the number here is now
measured rather than declared.

The fix does not rely on the schedule for resolution. Each run polls **every 5
minutes for 50 minutes** in a loop, so a late trigger costs coverage but never
granularity, and a new head is committed and tagged the moment it is seen
rather than at the end of the run. Check `poll-log.tsv` gaps, not the cron.

## Did the claims change, or only the proofs?

Rewriting a proof is unremarkable. Changing what you claim to have proved is
not. Upstream keeps no history, so nobody downstream can tell those apart. The
archive can. `tools/claims.py` regenerates [`claims.tsv`](claims.tsv) and
[`claim-churn.md`](claim-churn.md) from the tags.

Each challenge's JSON names the theorems it commits to proving. That list moved
twice:

| | released | 10:02 → 10:25 | 18:08 → now |
| --- | ---: | ---: | ---: |
| declared theorems | 40 | 41 | 38 |

Measured against the released state, **8 declared theorems are no longer listed
and 6 are new**. Both changes are worth stating precisely, because the headline
number is misleading in opposite directions.

**The seven de-listed spherical-codes theorems were not withdrawn.** All seven
are still declared and still proved in `MetricCodes.lean`. They were demoted
from the challenge's headline list behind consolidated `main_general`,
`strict_hierarchy` and `main_binary_theorem` statements. This is
re-headlining, not retraction.

**The one claim that genuinely disappeared was replaced by a stronger one.** At
release, `E_ConnesRigidity` asked for `¬ConnesRigidityAssertion`, where

```lean
def ConnesRigidityAssertion : Prop :=
  ∀ Γ Λ : CountableDiscreteGroup.{0},
    IsICC Γ → HasKazhdanPropertyT Γ → TracialGroupFactorsIsomorphic Γ Λ →
    IsICC Λ ∧ GroupsIsomorphic Γ Λ
```

Λ carries no hypotheses there. Refuting the implication only requires the
*conclusion* to fail, so a witness whose Λ is simply not ICC would discharge it
without saying anything about Connes' conjecture. From 10:02 the challenge
instead asks directly for

```lean
∃ Γ Λ, Group.FG Γ ∧ Group.FG Λ ∧ IsICC Γ ∧ HasKazhdanPropertyT Γ ∧
  IsICC Λ ∧ HasKazhdanPropertyT Λ ∧ TracialGroupFactorsIsomorphic Γ Λ ∧
  ¬ GroupsIsomorphic Γ Λ
```

which forces finite generation, ICC **and** Property (T) on *both* groups, plus
a second theorem producing an infinite pairwise non-isomorphic family. The
loophole is closed and the claim is strictly stronger.

**Nothing weakened, in any state.** Across all nine:

- every declared theorem resolves to a real declaration in the tree — 40/40,
  41/41, 38/38, never a dangling claim
- solution modules contain **zero** `sorry`, at every state
- the axiom allowlist never moves

**Which is the point.** The maintenance here was conscientious: a loophole was
found and closed, coverage went up, a build defect was repaired. None of it is
visible from upstream. A reader who forked at 07:42 and one who forked at 00:22
hold materially different mathematics, and neither can discover that, or that
the difference is an *improvement*. Silent revision costs an artifact its credit
for getting better, not just its cover for getting worse.

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

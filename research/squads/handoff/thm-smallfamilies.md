# Handoff: thm-smallfamilies (end of session 2, 2026-10-25)

- Branch `claude/thm-smallfamilies-formulas-49l6io`, draft PR #319. It carries the first session's branch
  `claude/small-degree-families-g7zllq` (rebased onto master) and this session's work.
- Write-up: `research/theorems/SMALL_DEGREE_FAMILIES.md` (ranked: proved, conjectured, weak patterns, dead ends).
  Scripts and saved outputs: `research/theorems/smallfam/`. Squad rounds: r2-smallfam, r3-smallfam in `LOG.md`.
- No new record in session 2. The (4,7) = 864 record of session 1 is on master.

## Where things stand

- Proved: the cyclotomic fibre bound for Z_p ⋊ Z_k (§2.3; tables at Δ = 3, 4, 5), the growth corollary (§2.4),
  and the (3,7) theorem for free actions with at most 8 orbits (§2.5).
- Complete negatives and screens are listed with their coverage in §2.5 and §6.2.

## Open items, cheapest first

1. (3,9), lifts of the 2+2 base: everything in 127–255 is exhaustively negative except order 128 (189 of 2,328
   groups done) and order 192 (1,543 groups, not run). Closing both would make "no 2+2 lift beats 506 at (3,9)" a
   theorem (`allgroups.py 3 9 N N --base bases/b22.txt --cycles 3 --abmax 112`).
2. (3,10): 2+2 lifts are done for 201–270 except 256; 271–511 are open. Haar graphs are done for 401–600 except
   512 and 576.
3. (4,8): the all-groups screen covers 1093–1400 except 1152, 1280, 1296, 1344. Near misses fade with N (best cost
   1 at 1100, 15 in 1251–1300, about 20 in 1301–1400), so going higher is unlikely to pay.
4. (4,9): order 2624 and the 54 non-squarefree orders in 2486–2700 that the installed GAP library lacks. They need
   the full SmallGrp data or direct constructions.
5. Δ = 5 fibre bound: only φ(o) ≤ 2 was tabulated; larger o needs a faster BFS than numpy.

## How to resume

- Prefix every command with `SCRATCH=<your scratch dir>`; the scripts otherwise default to an old path.
- `allgroups.py`, `fscreen.py`, `flscreen.py` and `sqfmeta.py` resume: they skip groups already in their output.
- Do not run two screens on the same orders at once without the per-process names (fixed in this session).
- Anchor `pkill`/`pgrep` patterns with `^python3 …`: an unanchored pattern also matches the shell that runs it.

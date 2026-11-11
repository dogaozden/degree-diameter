# c2 notes (deep-49 r1): split metacyclic Haar graphs of orders 2486..2530 not in SmallGroups

## What was done
- `mkcand.py`: enumerates Z_m x|_r Z_k with m*k = N for the 15 target orders, r^k = 1 mod m, d = ord(r mod m) >= 3,
  dedup r ~ r^t (t unit mod k). 325 groups before the |G/G'| = k*gcd(r-1,m) <= 309 filter, 264 after
  (`candidates.json`). N = 2488, 2490, 2528 have no split group with d >= 3 at all; 61 groups with d >= 3 were dropped by the q <= 309 filter.
- Tables: GAP builds G = <a,b | a^m, b^k, b a b^-1 a^-r> (pc group), checks |G| = N, exports with the FULL Aut(G)
  (export_group.g), build_tab.py makes the hx table. The first 30 groups and 7 slow ones used tools/mkmeta.py
  (a small subgroup of Aut) instead. Calibration: the same pipeline on the record group (seeds m71_35_49) finds 24+
  cost-0 sets in hx, so the search is working.
- Every automorphism generator is checked exhaustively (bijection, N^2 homomorphism test in numpy); no generator failed.
- `hx LIMIT 0` (own compiled copy `hx`, unchanged `hx.c`) over all x-orbit representatives, run by `driver.py`
  (resumable, time-boxed, progress from the stderr lines).
- Isomorphism dedup: `dedup.py` (invariant classes: element-order distribution, centre size, |G/G'|) gave 183 classes;
  `iso_run.py` (GAP IsomorphismGroups, slow for non-isomorphic pairs; only 12 of 81 pairs finished before the
  budget ran out). Confirmed duplicates so far: g2530_253_10_24 ~ g2530_11_230_2 (the other confirmed duplicates
  were already done separately and gave identical results). The other groups were run anyway.

## Result
- 263 distinct certified groups (all of the 264 candidates except one confirmed duplicate): hx LIMIT 0 gives
  `MIN >0` for every one, i.e. no Haar set of cost 0 (so no diameter-9 Haar graph with 2N vertices).
- Scoreboard lines: 263 lines with card "c2", score ">0", exact true, valid true (valid = exhaustive Aut check passed).
- Not done: the non-split metacyclic groups (GAP presentation with y^k = x^s) and the time left was not enough for them.

## How to rerun
- `python3 driver.py` (BUDGET=95 env, resumable; state in `state.json`; tables/logs in `runs/`).
- A single group: `gap -q --quitonbreak runs/KEY.g < /dev/null`, `python3 tools/build_tab.py runs/KEY.exp KEY`,
  `./hx KEY.tab KEY.aut 0 9 1 999999 KEY.hits`; `MIN >0` = none.

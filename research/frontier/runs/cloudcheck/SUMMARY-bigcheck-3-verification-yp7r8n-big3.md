# Big-record verification, job bigcheck-3

Branch `claude/bigcheck-3-verification-yp7r8n`. Verification only: nothing was searched, no checker code was edited, and no VALID verdict was written by hand. Each report holds the machine line, the file's sha256, the full stdout of the reference checker, then the full stdout of `bigcheck_indep` (built from `research/frontier/bigcheck_indep.c`, which is on `claude/bigcheck-indep-haar-cdziu4`).

## Results

All 8 files are VALID under both checkers.

| vertices | file | reference checker | ref verdict | bigcheck_indep |
|---:|---|---|---|---|
| 3,443,328 | d9D9_prod_psl_7_psl_7_61_orb3f0_s1 | build_haar2.py | VALID | VALID |
| 6,814,080 | d13D8_sl_64_13_orb3_s1 | build_haar2.py | VALID | VALID |
| 1,308,373,248 | d14D10_sl_193_91_orb3_FAST1_s1 | haarcheck_sl | VALID | VALID |
| 3,499,776 | d9D9_prod_psl_7_sl_7_31_orb3f0_s1 | build_haar2.py | VALID | VALID |
| 18,128,880 | d15D8_sl_109_7_orb3f0_s1 | haarcheck_sl | VALID | VALID |
| 208,029,120 | d15D9_sl_79_211_orb3f0_s1 | haarcheck_sl | VALID | VALID |
| 677,714,400 | d13D10_sl_199_43_orb3_s1 | haarcheck_sl | VALID | VALID |
| 1,316,504,400 | d14D10_sl_149_199_orb3_FAST1_s1 | haarcheck_sl | VALID | VALID |

Sol files are from `claude/structured-search-orbit-w5dd4f` (except `d13D8_sl_64_13_orb3_s1`, from `claude/cd-theory-beyond-random-3ybyf2`). The sha256 of each is in the first lines of its report:

- d9D9_prod_psl_7_psl_7_61_orb3f0_s1: f79e63d1bfd040bbbfb5f1ab766a833f4da2a25c4b4399b6cd9237154ce04dd7
- d13D8_sl_64_13_orb3_s1: c0b2e5f680a225b23ec6bd230ac66311ad9cb65735ec9f41d8dd52ac230145a3
- d14D10_sl_193_91_orb3_FAST1_s1: 1dbae081d82d33e8bf2a0f531206c4985188559fab2df589358d44db8d263607
- d9D9_prod_psl_7_sl_7_31_orb3f0_s1: 78a8b933bcc5459651ddd27ffa382eb3ae6c9e2cb62ec565d751fe6fdc7afcae
- d15D8_sl_109_7_orb3f0_s1: 8142bd2301db5339179f1c976e4fc4a9322e226221007a6647449db8eaa37846
- d15D9_sl_79_211_orb3f0_s1: f6cd4267522ffd09e6cdc5497a7a68018516cb306b4aa73609605e9f56f38b1a
- d13D10_sl_199_43_orb3_s1: 9854750c484f375ca4eb497a7ab9d38139c2715d453da5396b5b4fa8c1bb0384
- d14D10_sl_149_199_orb3_FAST1_s1: 9c68d3332532bbd1b82feeb48d870bc2c1184a7d10f41086cfbc661a71d03e49

## Method

* Reference checker: `haarcheck_sl` (built from `research/frontier/haarcheck_sl.c`) for `sl` over a prime field; `build_haar2.py` for prod files and for `sl` over GF(64). `haarcheck_psl` was not needed. The reference never ran out of memory, so no report says "does not fit".
* Each file was copied from its branch to `research/frontier/sols/` and was not committed.
* Each report was committed on its own and pushed after the file's checks finished.

## Watch

* Window: about 01:15 to 05:32 UTC on 2026-10-24. Ten 20-minute cycles fetched all `origin/claude/*` refs. Candidates were the largest unreported file in each (d, D) cell among `sol` files above 2,000,000 vertices on `claude/structured-search-orbit-w5dd4f` and `claude/structured-haar-search-ws7bet`.
* The last candidate, `d14D10_sl_149_199_orb3_FAST1_s1`, appeared in the cycle ending 05:03 UTC. Its check ran to 05:32 UTC, past the 4-hour mark.
* Cycles that found no candidate: 2, 3, 7, 8, 9.

## Caveats

* One machine: 4 cores, 15 GB RAM.
* These reports record stdout only. Wall times and peak memory were not recorded, unlike the earlier SUMMARY-big.md.
* The independence caveat from the earlier job still applies: `bigcheck_indep` and the reference checkers read the same file format and conventions, so a shared misreading of a convention would not be caught.

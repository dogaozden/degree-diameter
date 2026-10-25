# Handoff: job cell-12-8 (state at the end of round 2, 2026-10-25)

Branch claude/cell-12-8-search-qhi11t (draft PR #356). Read research/squads/cells/d12D8.md first.

- Done: the (12,8) table value 4,650,100 (Gómez thesis §2.9.3, ΩH₉) has diameter 9 (proof plus checks at
  q = 3, 5, 7, 9; three independent implementations). Best valid (12,8) graph: Haar PSL(2,59) × Z19, 3,901,080,
  build_haar2 VALID (research/frontier/sols/d12D8_psl_59_19_orb3f0_w3_s1.txt).
- Possibly still running when the session ended: k = 3 rungs from research/d12D8/haar/spool/*.cmd (pool.sh):
  PSL(2,67) × Z13 (3,909,048), PSL(2,27) × Z199 (3,911,544), SL(2,47) × Z19 (3,943,488). Any new solution file
  d12D8_*.txt in research/d12D8/haar/ with a RESULT best=0 log line needs build_haar2.py before it counts.
- Not worth more compute for beating 4,650,100: Haar's first-moment ceiling is 4,529,596; hexagon constructions
  (lifts, hubs, affine products) are far below Haar. Leads: cell report, last section.

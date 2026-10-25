# D = 7 family: tonight's hexagon constructions carried to the other D = 7 cells (job d7-family)

Session: claude/d7-family-hexagon-mrr6hp, 2026-10-25 (16:13–22:30 UTC). Opus with Haiku squads (rounds d7fam-r1, d7fam-r2,
research/squads/LOG.md). Tools in research/d7family/.

The three constructions (all on the split Cayley hexagon H(q)):
- mirrored surgery (research/theorems/MIRRORED_SURGERY.md, research/cell147/mirror/): a point set R' and a bijection
  sigma with R' non-collinear, sigma(R') non-concurrent and sigma a local duality at every point of R'; frees R' on a
  non-friendly transition;
- typed levels (research/squads/cells/d16D7.md): levels of type H or H^D, identity matchings on friendly transitions
  (types differ), any non-collinear / non-concurrent set freed there;
- relaxed friendly sets (research/d15D7b/RELAXED.md): collinear (concurrent) pairs allowed in a friendly freed set when
  hubs are wired to cover elements incident with the partner.

## Results

RESULTS_TABLE

## Which construction applies where

- **Typed levels need at least five levels.** With three levels (cells (7,7), (9,7), (10,7), (11,7), (13,7), one
  matching per class) the matchings form a 3-cycle, so one transition is always non-friendly, and hubs need a free slot
  in every level: n = 3·|I(H(q))| + 2·min(|R_H|, |R_L|, |R'|) = the mirrored value. Only larger mirrored sets help.
- **Five levels (types HDHDH) is the only good pattern** for (14,7) and (16,7): with two adjacent D levels some level
  has no friendly outgoing transition. In HDHDH all six friendly transitions are bottlenecks
  (KB = N + min(P01, L12, P23, P41, L34 + L30 − N), KA = N + min(L30, L12, P23, L34, P01 + P41 − N), N = |R'|), so the
  covers of every relaxed set must come from the other bottleneck sets (no private covers as in (15,7)).
- **H(9) cells (11,7), (12,7):** H(9) is self-dual and every matching there is already a duality, which is what typed
  levels emulate; the records use the spread construction (7,300 freed points per level and shift, cap 14,600 hubs per
  side at (12,7), research/squads/cells/d12D7.md §3). Relaxed sets cannot beat it: the collinearity graph of H(q) has
  degree q(q+1) and smallest eigenvalue −(q+1), so a point set in which every point is collinear with at most one other
  has at most N(1 + q + 1)/(q + 1)² points (Hoffman-type bound for induced subgraphs of maximum degree 1), i.e.
  66,430·11/100 = 7,307 at q = 9, against the 7,300 already freed. No new value there.

DETAILS

## Files

FILES

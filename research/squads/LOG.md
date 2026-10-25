# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 04:47–05:45 UTC, hexagon-family (Opus lead, cloud session), round hexfam_r1
Goal: larger freed sets for the D = 7 hexagon records: partial ovoids of Q(6,q) (q = 5, 7, 8, 11, 13; best 72, 288,
217, 756, 792) and non-collinear sets of H(9) (best 4,291). Scorer: research/projects/hexagon-family/tools/povcheck.
Cards (one line each) and best score:
- c1 PSL(2,q) on binary sextics, orbit unions + max-weight clique: q7 288 (tie), q11 336, q13 196.
- c2 J1 < G2(11) and 2^3.L3(2) on octonions, orbit cliques: q11 756 (tie, a different 756 set), q13 504 (no full report).
- c3 cyclic tori of order q^3+1 and q^3-1, orbit cliques: q5 72 (tie), q7 288 (tie), q11 148.
- c4 W(E7) reflection subgroups and monomial groups: q5 ≤ 60 so far (no report at log time).
- c5 ARW-style swap search from the best sets: no gain at any q; every outside point of the q = 11 set is orthogonal
  to 60–78 of its points (no 1-, 2-, 3-tight points), so swaps cannot work there.
- c6 ARW iterated local search on the collinearity graph of H(9) from the 4,291 set: **4,306** (new).
- c7 q = 8: Sp(6,8) torus of order 513 orbits (≤ 76) and ILS from 217: no gain.
- c8 wildcard, affine chart opposite e4 with random cyclic similitude groups: q11 262; proved that 2-dim
  anisotropic translation subgroups cannot be combined.
Kept: c6's 4,306 → (11,7) 407,192 (all-pairs VALID here). Separately (Opus): a Haar graph of PSL(2,11)×Z13 (Δ = 7,
D = 7, 8,580 per side) as the (12,7) hub graph → (12,7) 681,460 (all-pairs VALID here). Next: long ARW runs at q = 9
(Opus), round 2 with structured groups (G2 root elements now in tools/g2gens.py) and stabilizer-subgroup orbit search.

## 2026-10-25 05:45–06:30 UTC, hexagon-family (Opus lead), round hexfam_r2
Goal: as r1 (q = 9 now 4,306). Cards and best score:
- c1 q9, orbit unions of G2(3)/G2(9) subgroups (root elements in tools/g2gens.py) + ARW: no report at log time.
- c2 q9, CP-SAT with the 4,306 hint (1 worker, 1200 s) and own exact LNS (regions up to 3,500 candidates): 4,306
  (tie; only plateau moves; CP-SAT bound 13,031).
- c3 q11, orbit-level search over W(E7) mod 11 subgroups: 756 (tie). Found that the 756 set is a union of whole
  W(E7) orbits, so every subgroup sees it as orbit union; all subgroups tried top out at exactly 756.
- c4 q13, W(E7)/W(E6) reflection subgroups (exact + orbit ILS), SL3(13)/torus subgroups: 792 (tie); 11 distinct
  792 sets found, none extends.
- c5 q5/q7 CP-SAT in the affine chart: no report at log time (q5 log: 69 + e4 = 70 found, bound 154).
- c6 q8, Sp(6,2) subfield subgroup orbits: 217 (tie); Sp(6,2) has 5 orbits on PG(5,8), none usable.
- c7 mixed-set probe: interim files show 35 at q = 4 (pure ARW 31) and 48 at q = 5 (pure structured 72). Its
  q = 4 35-set passes Lemma 3 (56 midpoints) and gives a diameter-7 graph (checked by Opus).
- c8 wildcard, tensor split GF(q)^3 (x) GF(q)^2 + 1 with SO3: q11 122, q13 326 (dead end).
Kept / next (Opus): the squad result that mattered is c7's: mixed freed sets really work (Lemma 3). Opus turned it
into Proposition 4 of THEOREM.md (add pairwise opposite points x with lines s_x to a record pure set, S chosen inside the spread
by cell counting): (7,7) 23,596 (72 + 8), all-pairs VALID; runs at q = 7, 8, 11, 13 in progress. Unions of the
distinct 792 / 756 sets (ARW on their union, 7,419 and 2,123 points) give nothing above 792 / 756.

## 2026-10-25 06:45–07:45 UTC, hexagon-family (Opus lead), round hexfam_r3
Goal: evolve the extension (THEOREM.md Prop. 4: add points x with lines s_x to a pure record set R, cell counting
in the spread). Score = K from ext/mixsol.py (Lemma 3 check, sigma, (R2)). Bars: q11 768, q13 815, q8 232, q7 296,
q5 81. Cards and best score:
- c1 q11, destroy-and-repair on the added pairs (remove 1-3, greedy re-add, 20k sampled lines), from 769: 769.
- c2 q11, relaxed Lemma 3 greedy (added points may be at distance 4 from each other): 767; relaxation fires rarely.
- c3 q11, greedy over ALL 175,824 non-spread lines (no sampling), candidates ranked by overlap with covered R-points:
  **770** (756 + 14). Every order stalls at 13-14 added points: no candidate keeps a feasible line.
- c4 q13, extension from a different pure 792 set (E6 + A3A1A1 type) and a repair resume: **816** (792 + 24).
- c5 q11, R moved by reflections, other 756 set, Hermitian spread: 768 for every position; plateau at 12 adds.
- c6 q5/q7/q8, destroy-and-repair ILS over all non-spread lines: 81 / 296 / 232 (ties).
- c7 q11, exchange (remove one R-point, add pairs): 768; no single-removal fixer exists in its 300-line sample.
- c8 q13, disjoint-neighbourhood CP-SAT on a pool of 600 pairs: 798. Notes min |N(x) cap R| = 24 at q = 13, so a
  disjoint family is limited by the line side, not by R.
Kept / next (Opus): c3's all-lines scan (ext/ext_all.py), rerun by Opus on 30 seeds at q = 11 (ext/allscan, logs in
ext/logs): 18 seeds give 769, 12 give 770, none 771. Opus built (13,7) 1,064,476, (14,7) 1,774,640, (15,7)
2,484,804 from the 770 set and (16,7) 4,025,604 from c4's 816 set (checks in research/projects/hexagon-family/checks).
The greedy is exhausted at q = 11; a gain needs a move that changes R itself or a non-greedy exact search on the
cells. Stray actions: c1 left a tail -F monitor (killed); c7 and c8 first ended their turns while waiting on a
monitor and reported later.

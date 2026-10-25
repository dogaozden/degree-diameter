# hexagon-family: handoff

Branch `claude/hexagon-family-blvamb` (Opus lead, cloud session, 2026-10-25 04:30–). Brief: BRIEF.md. Draft PR #331.
Theory: THEOREM.md. Lean: lean/BipartiteDD/HexagonD7/. Squad rounds: research/squads/hexfam_r1..r3 (LOG.md).

## Graphs (all checked here; records/README/RESULTS not edited)

| cell | record at start | new | freed set | files (sols/, also in research/frontier/sols/) | check (checks/) |
|---|---|---|---|---|---|
| (7,7) | 23,580 | **23,600** | H(5): 72 pairwise opposite + 10 added (Prop. 4; ext_all.py seed 134, order ovl) | sets/P5_mix82.pairs, d7D7_hex5_mixK82_n23600.sol | apsp_mt all pairs VALID |
| (9,7) | 118,224 | **118,240** | H(7): 288 + 8 | sets/P7_mix296.pairs, d9D7_hex7_mixK296_n118240.sol | apsp_mt VALID |
| (10,7) | 225,128 | **225,160** | H(8): 217 + 16 (all-lines scan ext_all.py, seed 2, order ovl) | sets/P8_mix233.pairs, d10D7_hex8_mixK233_n225160.sol | apsp_orb VALID (225,158 from 217 + 15: apsp_mt VALID) |
| (11,7) | 407,162 | **407,192** | H(9): 4,306 non-collinear points, σ = duality | sets/P9_ncol_4306.txt, d11D7_hex9_B2dualK4306_n407192.sol | apsp_mt VALID |
| (12,7) | 680,068 | **681,520** | same 4,306; 5 levels; Haar hub graph of (Z41 ⋊ Z10) × Z21 (8,610/side; r = 4) | hubs/h_meta41x10x21.txt, d12D7_hex9_B2dual5K4306_H8610.hubs (frontier: ..._n681520.{sol,hubs}) | apsp_orb VALID (681,460 with PSL(2,11)×Z13: apsp_mt VALID) |
| (13,7) | 1,064,448 | **1,064,476** | H(11): 756 + 14 | sets/P11_mix770.pairs, d13D7_hex11_mixK770_n1064476.sol | apsp_orb VALID (35 min, 1 thread) |
| (14,7) | 1,774,584 | **1,774,640** | same 770, 5 levels | d14D7_hex11_mixK770_n1774640.hubs (+ the (13,7) .sol) | apsp_orb VALID (38 min, 2 threads) |
| (15,7) | 2,484,720 | **2,484,804** | same 770, 7 levels | d15D7_hex11_mixK770_n2484804.hubs (+ the (13,7) .sol) | PENDING (apsp_orb L=7) |
| (16,7) | 4,025,508 | **4,025,604** | H(13): 792 + 24, 5 levels | sets/P13_mix816.pairs, d16D7_hex13_mixK816_n4025604.{sol,hubs} | PENDING (apsp_orb L=5, running) |

Also checked: (13,7) 1,064,472 from the 768 set (sols/d13D7_hex11_mixK768_n1064472.sol, apsp_orb VALID), superseded.
apsp_orb (research/lifts/coordinator_check/apsp_orb.c) first verifies that the level shift (x, i) -> (x, i+1) is an
automorphism, then runs BFS from every vertex of level 0 and every hub; usage `apsp_orb EDGES d D threads L 2N`.

## Rebuild (from this folder; hex/ is local)

    gcc -O3 -o tools/hexgen2 ../../d10D7/hexgen2.c && (cd hex && ../tools/hexgen2 11)   # also 5 7 8 9 13
    gcc -O3 -o tools/d7hex ../../d10D7/d7hex.c -lm
    gcc -O3 -o tools/xgen ../../d10D7/dual/xgen.c
    gcc -O3 -pthread -o tools/apsp_orb ../../lifts/coordinator_check/apsp_orb.c
    # 3 levels: (7,7) (9,7) (10,7) (13,7)
    ./tools/d7hex edges hex/hex_q11.bin sols/d13D7_hex11_mixK770_n1064476.sol e13.txt
    ./tools/apsp_orb e13.txt 13 7 3 3 354312
    # 5 / 7 levels: (14,7) (15,7) (16,7)
    ./tools/xgen hex/hex_q11.bin sols/d13D7_hex11_mixK770_n1064476.sol sols/d14D7_hex11_mixK770_n1774640.hubs 5 e14.txt
    ./tools/apsp_orb e14.txt 14 7 3 5 354312
    ./tools/xgen hex/hex_q11.bin sols/d13D7_hex11_mixK770_n1064476.sol sols/d15D7_hex11_mixK770_n2484804.hubs 7 e15.txt
    ./tools/apsp_orb e15.txt 15 7 3 7 354312
    ./tools/xgen hex/hex_q13.bin sols/d16D7_hex13_mixK816_n4025604.sol sols/d16D7_hex13_mixK816_n4025604.hubs 5 e16.txt
    ./tools/apsp_orb e16.txt 16 7 3 5 804468
    # (11,7): ./tools/d7hex edges hex/hex_q9.bin sols/d11D7_hex9_B2dualK4306_n407192.sol e11.txt; apsp_mt e11.txt 11 7 3
    # (12,7): hub graph from the Haar solution (research/frontier/build_haar2.py hubs/h_meta41x10x21.txt hg.edges:
    #   VALID d=7 D=7 N=8610); hub j (each side) owned by freed point j mod 4306, hub edge j ~ k from Haar edge (j, 8610+k)
    gcc -O2 -o tools/x5gen2 ../../d10D7/dual/x5gen2.c
    ./tools/x5gen2 hex/hex_q9.bin sols/d11D7_hex9_B2dualK4306_n407192.sol sols/d12D7_hex9_B2dual5K4306_H8610.hubs e12.txt
    ./tools/apsp_orb e12.txt 12 7 3 5 132860

hex/hex_q11.bin sha256 e60db369..., hex_q13.bin 57aa5dfc... (tools/hexgen2 output, deterministic).

From a pairs file (freed point, its line) to the files: `python3 ext/mixsol.py q PAIRS PREFIX 1 3,5,7` (the 816 files: `... 13 sets/P13_mix816.pairs PREFIX 1 5`) checks
Lemma 3 independently (distances, midpoint -> midline map), builds σ, verifies (R2) at every freed point, picks a
hub graph and writes PREFIX.sol (3 levels, d7hex format) and PREFIX_LV5/7.hubs.

## How the sets were found

- Pure sets (pairwise opposite): the records of research/d10D7/sets (q = 5, 7, 8, 11, 13). Three squad rounds
  (orbit unions of G2/E7-type subgroups, swaps, CP-SAT, LNS) tie them and never beat them; the 756 set at q = 11 is a
  union of W(E7) orbits, every outside point is at distance 4 from 60–78 of its points (no swaps exist).
- Extension (THEOREM.md Prop. 4, Lemma 3/3'): add points x at distance 4 from some points of R with lines s_x, cell
  counts in the Hermitian spread. ext/extend5.py (sampled lines), ext/ext_all.py (all lines; q = 11: 30 seeds, 18 give
  769 and 12 give 770, none 771; logs in ext/logs). q = 13: 816 from another 792 set (squad r3 c4).
- q = 9: duality, any non-collinear set; ARW (q9/arw.c) 4,306 (Hoffman bound 6,643).
- q = 16: elliptic quadric, 257 pairwise opposite points (sets/P16_ell257.txt); graph not built ((18,7), 6.7M vertices).

## Lean (lean/BipartiteDD/HexagonD7/, standard axioms only, Axioms.out.txt)

Build: `cd lean && lake build BipartiteDD.HexagonD7.Midpoints` (PATH=$HOME/.elan/bin), axioms:
`lake env lean BipartiteDD/HexagonD7/Axioms.lean`. Theorem 1 (`Hyp.ediam_le`, `exists_graph`), `table_family`,
Lemma 2 (`exists_local_duality`), `freed_family`, `certificate` (pairwise opposite, 3 levels), Lemma 3' (`exists_r2_iff`,
both directions), duality case (`duality_r2`), Lemma 3 for midpoints shared by two points, i.e. Prop. 4
(`exists_r2_of_near`, Midpoints.lean), `certificate_mixed` (any j, mixed sets: the three finite checks on R/S,
the counts, and the hub graph give the graph). Not formalised: a duality of H(3^h); the finite checks of the actual sets.

## Open / next

- q = 11: the extension greedy is exhausted at 770 (every order stalls at 13–14 added points). A gain needs a move that
  changes R itself, or an exact search over the cells (squad r3 c8: CP-SAT on a 600-pair pool, too small).
- q = 13: 816; more seeds/resumes of the c4 repair from other 792 sets might add a few.
- q = 9: 4,306 vs 6,643. (12,7) uses 8,610 of the 8,612 possible hubs per side (hubs/scan: groups of order
  8,581–8,612; order 8,612 = 4·2,153 metacyclic fails, 8,611 has only the cyclic group).
- Pending checks: see the table; outputs go to checks/d1{3,4,5,6}D7_n*_apsp.txt.

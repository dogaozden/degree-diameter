# hexagon-family: handoff

Branch `claude/hexagon-family-blvamb` (Opus lead, cloud session, started 2026-10-25 04:30 UTC). Brief: BRIEF.md.

## State

**Graphs built and checked all-pairs here (apsp_mt, no symmetry assumed):**

| cell | old record | new | how | files | check |
|---|---|---|---|---|---|
| (11,7) | 407,162 | **407,192** | H(9), duality matching, 4,306 non-collinear freed points (squad hexfam_r1 c6, ARW from the 4,291 set) | sets/P9_ncol_4306.txt, sols/d11D7_hex9_B2dualK4306_n407192.sol | `n=407192 edges=2239556 degree min=11 max=11 bipartite=yes diameter=7, RESULT VALID d=11 D=7` (checks/d11D7_n407192.sha256) |
| (7,7) | 23,580 | **23,596** | H(5), 72 pairwise opposite + 8 mixed freed points (THEOREM.md Prop. 6, `ext/extend2.py`), σ from Lemma 3 (`ext/mixsol.py`) | sets/P5_mix80.pairs, sols/d7D7_hex5_mixK80_n23596.sol | `n=23596 edges=82579 degree min=6 max=7 bipartite=yes diameter=7, RESULT VALID d=7 D=7` (checks/d7D7_n23596_apsp.txt) |
| (12,7) | 680,068 | **681,460** | same 4,306 freed points, 5 levels; hub graph = Haar graph of PSL(2,11)×Z13 (Δ 7, D 7, 8,580 per side) | sols/d12D7_hex9_B2dual5K4306_H8580.hubs, hubs/h_psl11x13.txt | `n=681460 edges=4088600 degree min=11 max=12 bipartite=yes diameter=7, RESULT VALID d=12 D=7` (checks/d12D7_n681460_apsp.txt, sha256 file) |

Rebuild (from this folder; hex/ is local, made by `tools/hexgen2 9`):

    gcc -O3 -o tools/hexgen2 ../../d10D7/hexgen2.c && ./tools/hexgen2 9
    gcc -O3 -o tools/d7hex ../../d10D7/d7hex.c -lm
    gcc -O3 -pthread -o tools/apsp_mt ../../lifts/coordinator_check/apsp_mt.c
    # (11,7)
    ./tools/d7hex edges hex/hex_q9.bin sols/d11D7_hex9_B2dualK4306_n407192.sol e407192.txt && ./tools/apsp_mt e407192.txt 11 7 3
    #   (the .sol was made by: B2PTS=sets/P9_ncol_4306.txt ./tools/d7hex b2dual hex/hex_q9.bin \
    #    ../../frontier/sols/d11D7_hex9_B2dualK4291_n407162.sol 1 OUT.sol 8 0 ; M = the duality phi of that file)
    # (12,7)
    gcc -O2 -o tools/x5gen2 ../../d10D7/dual/x5gen2.c
    ./tools/x5gen2 hex/hex_q9.bin sols/d11D7_hex9_B2dualK4306_n407192.sol sols/d12D7_hex9_B2dual5K4306_H8580.hubs e681460.txt
    ./tools/apsp_mt e681460.txt 12 7 3
    #   hub graph: ../../frontier/build_haar2.py hubs/h_psl11x13.txt hg.edges (VALID d=7 D=7 N=8580, sha256 be78483c...);
    #   hub j (each side) owned by freed point j mod 4306; hub-graph edge j ~ k from Haar edge (j, 8580 + k).

Mixed extension (any q with a pure record set): `python3 ext/extend2.py q RSET SPREAD OUT.pairs seed tries maxadd`
(R = record set, SPREAD = its line set, e.g. research/d10D7/sets/L5_c6_126.txt), then
`python3 ext/mixsol.py q OUT.pairs PREFIX seed 3,5,7` (checks Lemma 3, builds σ, verifies (R2), writes PREFIX.sol and
PREFIX_LV5/7.hubs), then `tools/d7hex edges` (3 levels) or `tools/xgen HEXBIN PREFIX.sol PREFIX_LVm.hubs m OUT`
(m = 5, 7) and apsp_mt / apsp_orb.

**Theory:** THEOREM.md (Theorem 1 for 2j+1 levels and freed points with a local duality, Lemma 2 for pairwise
opposite sets, Lemma 3 characterisation, bounds Prop. 4–5).

**Lean:** lean/BipartiteDD/HexagonD7/ (Defs, Cover, Diam, Main, Hexagon, Axioms + Axioms.out.txt). Proved: Theorem 1
for any incidence structure with point–line walks ≤ 5 and ≥ 2 lines per point / points per line
(`Hyp.ediam_le`, `exists_graph`, with degrees and order), and `table_family`: for every finite field F, q = |F|,
j ≤ q, a bipartite graph of max degree q+1+j, diameter ≤ 7, 2(2j+1)(q+1)(q⁴+q²+1) vertices. Only standard axioms.
Build: `cd lean && lake build BipartiteDD.HexagonD7.Hexagon`.

**Searches:** squad rounds in research/squads/hexfam_r1, hexfam_r2 (LOG in research/squads/LOG.md). Tools:
tools/povcheck (scorer), tools/q6lib.py, tools/g2gens.py (G2 root elements), prod/mis.c (generic ARW MIS),
ldual/ldual.c (mixed-set greedy), q9/arw.c (ARW for q = 9).

## Open / next

- q = 11, 13: no improvement on 756 / 792 yet (round 1: point swaps impossible, every outside point of the 756 set is
  orthogonal to 60–78 of its points).
- q = 9: ARW stalls at 4,306; bigger R also needs a bigger Haar hub graph for (12,7) (any group of order ≤ 2|R|).
- Lean: done so far also Lemma 2 (`exists_local_duality`), greedy opposite sets, and `freed_family`
  (n_b(q+2,7) ≥ 6(q+1)(q⁴+q²+1) + 2(q−1) for every finite field). Not formalised: the q = 3^h duality case, and the
  specific record sets (their pairwise-opposite / hub-graph checks are computer checks, too big for the kernel).

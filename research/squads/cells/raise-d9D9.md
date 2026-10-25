# Cell (9,9): raise the orbit-symmetric Haar record (job raise-9-9, round 2)

Record to beat: **3,499,776** (= 2·N, N = |PSL(2,7) × SL(2,7) × Z_31| = 1,749,888; k = 3, m = 3, f = 0, μ = 30.5;
file research/frontier/sols/d9D9_prod_psl_7_sl_7_31_orb3f0_s1.txt). Table 2,961,536; Moore bound 38,347,922.

Round 1 (branch claude/raise-d9d9-record-4vxjz9, notes in its cells/raise-d9D9.md): 16 annealing runs of 3,000–3,600 s on
sl 29 73, sl 121 1, prod sl 9 psl 17 1, prod sl 4 sl 31 1, prod psl 3 sl 13 67 (k = 3, f = 0). Best costs 6–20, none
reached 0. Round 1 ended with: "not raised", and listed as untried: more core-hours at μ 31–33, metacyclic lifts, f = 3,
SL(3,q) centralizers.

## Round 2: what was tried (this branch)

Code: research/structured/haar_sym.c gained a `GENS` mode (env `GENS="c:r,..."`, `GENSCAN=1` or `GENSAMPLE=m`,
`FINDCONJ=o`, `QINV=i`, `GENSDBG`, `LEVELS`). S is the orbit of one point under a group B of automorphisms
x ↦ (c x c⁻¹, r z), accepted when |Bx| = d. Solutions (cost 0) are written with the full diameter check.
The point of the mode: a single orbit of size 9 has ~N/9 candidates, so one can scan all of them (≈ 8 min per group
at 2.6 ms per evaluation) instead of annealing. If the Poisson model held (ε ≈ 2, see SIZE_LAW §2.2) a group with
μ ≈ 30 would have ~10² solutions among those N/9 orbits.

Results (D = 9, d = 9 unless noted; costs are uncovered elements):

| group | N | B | random-S min (samples) | orbit min | reading |
|---|---|---|---|---|---|
| sl 17 × Z_361 (9-scaling) | 1,767,456 | Z9 = ⟨(c_g9, r9)⟩ | RANDSAMPLE 328–338 | 446 (2,000) | cyclic Z_361 mixes badly |
| psl 19 × Z_523 (9-scaling) | 1,788,660 | Z9 | 417 (2) | 562 (2,000) | same |
| psl 19 × Z_79 at D = 8 (9-scaling, r of order 3) | 270,180 | Z9 | 26 (200) | 122,694 | σ³ fixes all of Z_79: ball growth collapses |
| prod psl 7 sl 7 × Z_31 (record group) | 1,749,888 | Z3² = ⟨(c_x, 5), (c_y, 1)⟩ | 42 (K = 3 family) | 2·10⁶–3·10⁶ | orbits generate small subgroups (|⟨S⟩| = 10⁴–2.5·10⁵) |
| meta 583296 ⋊ Z_3 | 1,749,888 | — | RANDSAMPLE 9.9·10⁵ | — | abelian index-3 subgroup: dead |

Reading. A cyclic order-9 automorphism needs every prime of n to be ≡ 1 mod 9 (so that σ³ has few fixed points), and
that rules out every group in the window with a large nonabelian factor. A Z3² acting on a Z_p factor always has an
element trivial on Z_p, with fixed set |C_Q| · p, and on the record group those orbits mostly fail to generate G.
So the K = 9 idea does not work with the groups available at this order.

Triple and pair products in the window (enumerated; solvable factors SL(2,3)/PSL(2,3) dropped as poor mixers):
prod psl 5 psl 5 × Z_487 (N 1,753,200, μ 31.2, |Fix| 8): random K = 3 orbits min 225, median 2,373. Dead: the cyclic
factor 487 is too large for a 3,600-element nonabelian part. The other window groups with small |Fix| are either already
in round 1's screen or have a cyclic factor of similar size.

Rungs of the K = 3 family (this round, 1 h each, K 8, THREADS 1): see the table at the end (filled in when done).


# Next cells: what our machinery gives (ranked)

frontier-opus, 2026-10-22. Table values: TABLE.md (DS14v2 Table 4 = wiki, March 2013; D = 3 column updated to AL 2022).
Heuristic and code: heuristic.py, haar_gen.c, build_haar.py in this folder.

## 0. What is left

Open cells with Δ ≤ 16, D ≤ 10 that we do not hold and that are not known optimal:

- D = 3, 4, 6: none. Every cell is either a Moore graph (Δ−1 a prime power), (7,3) = 80 (proved optimal), or ours.
- D = 5: Δ = 6, 10, 11, 12, 13, 14, 15, 16 ((3,5) = 56 is optimal). Δ = 6, 8 and 10 are being searched by the D = 5
  agent (d5-hunt-haiku).
- D = 7, 8, 9, 10: all 56 cells. No Moore graphs exist for D ≥ 7 (Feit–Higman: no octagon of order (q,q), q ≥ 2).

## 1. Geometry (doubling, whiskers, levels, hats): nothing new in the open cells

Exact counts. Every geometric construction we have lives at D = n for a generalized n-gon.

- **n = 3, 4, 6:** all cells done (Moore, or ours via AL+2 hats, Theorem A / C1, Theorem D / R).
- **n = 8 (Ree–Tits octagon GO(2,4), the only one with max degree ≤ 16):** 1755 points of degree 5, 2925 lines of
  degree 3; incidence graph 4680 vertices, max degree 5, D = 8. Points already have degree Δ = 5, so a doubled set
  (Delorme, Theorem 1) can contain no line, and condition (b) forces a partial ovoid (each line sees ≤ 1 doubled point).
  Tripling (m = 3) a partial ovoid gives at most 4680 + 2·2925/5 = **5850 < 9234** = table (5,8). Twins of points with
  ≤ 2 per line (a weighted 2-ovoid) give the same 5850. GO(8,64) has degree 65: out of range. **Dead.**
- **GQs and hexagons at D = n + 1 (D = 5 from GQ(q,q), D = 7 from H(q)):** the order is capped by the polygon plus
  (m−1)·(number of doubled vertices) ≤ (m−1)·2N/q, while the table at D = n+1 is ~q times larger than the polygon.
  Example: (13,5) from GQ(11,11): 2928 + O(q³) ≪ 11480. (15,7) from H(13): 804468 + 2q⁴·… ≈ 870440 (our (15,6)
  graph also has diameter ≤ 7) ≪ 2480184. **Dead** at every open cell.
- **Non-classical GQs (T2(O), Q(5,q), H(3,q²), H(4,q²)):** orders (q,q) give the D = 4 Moore cells; unequal orders
  (q,q²), (q²,q), (q²,q³) have max degree q²+1 or q³+1 and only fit at Δ = 5, 10 (q = 2, 3) where D = 4 is Moore.
  **Nothing.** Hexagon duals H(q)^D have the same graph. Covers of a girth-12 graph cannot have diameter 7 (a
  voltage-1 closed walk of length ≤ 13 needs a 12-cycle through the pair; pairs at distance ≤ 4 fail).
- **Hat gadgets:** D = 3 only; all D = 3 cells done.
- **m-ary levels, Δ = q + m:** only improve D = 6 (done; (16,6) uses m = 3).

So the open cells are all "computer" cells: D = 5 (Loz–Pérez-Rosés–Pineda-Villavicencio voltage lifts) and D ≥ 7.

## 2. Haar graphs (lifts of the Δ-dipole) at D ≥ 7

Haar graph H(G,S): (g,A) ~ (sg,B), |S| = Δ. Right multiplication is transitive on each side, so the diameter is the
larger of two eccentricities. Coverage: D odd = 2k+1 needs (S⁻¹S)^k = G and (SS⁻¹)^k = G; D even = 2k needs
S(S⁻¹S)^(k−1) ∪ … ∪ S = G (one condition; the other side is its inverse), plus the same-side condition (automatic in
practice).

**Heuristic.** W = number of reduced words on the binding side (D odd: 1 + Σ Δ(Δ−1)^(2i−1), i ≤ k; D even:
Δ Σ (Δ−1)^(2i), i < k). If words were independent uniform elements, a cover exists roughly when
N e^(−W/N) < Δ ln N, giving a side order N_h. Calibrated on our D = 5 records: achieved ≈ 0.87–0.89 N_h at Δ = 8, 9.
The column "need" is (table/2)/N_h: below ~0.85 the cell should be within reach of the search.

Measured (this session): at (7,8) random S over SL(2,13)×Z₁₉, PGL(2,19)×Z₆, PSL(2,23)×Z₇, Z₁₃₈₁⋊Z₃₀ (N ≈ 41–42.5K)
start with 24–131 uncovered elements (worse than independence, which predicts ~12); annealing with targeted moves
(make an uncovered element adjacent to a random walk) gets to 1–2 uncovered within a minute.

## 3. Ranked targets

| rank | cell | table | need N > | N_h | need/N_h | expected order (0.87 N_h) | gain | cost per evaluation |
|---|---|---|---|---|---|---|---|---|
| 1 | (7,8) | 80,940 | 40,470 | 51,523 | 0.79 | ~89,600 | +10% | 0.6 M steps, ~500/s |
| 2 | (8,8) | 201,480 | 100,740 | 132,565 | 0.76 | ~230,700 | +14% | 1.6 M steps, ~200/s |
| 3 | (8,9) | 1,091,232 | 545,616 | 759,500 | 0.72 | ~1.32 M | +21% | 9 M steps; bigcheck hours |
| 4 | (9,8) | 449,480 | 224,740 | 303,728 | 0.74 | ~528,500 | +18% | 4 M steps |
| 5 | (7,9) | 400,160 | 200,080 | 252,781 | 0.79 | ~439,800 | +10% | 2.8 M steps |
| 6 | (6,10) | 452,032 | 226,016 | 295,200 | 0.77 | ~513,600 | +14% | 2.7 M steps |
| 7 | (6,9) | 117,360 | 58,680 | 70,204 | 0.84 | ~122,100 | +4% | 0.7 M steps |
| 8 | (8,7) | 40,586 | 20,293 | 24,086 | 0.84 | ~41,900 | +3% | two BFS, 0.3 M steps |
| 9 | (6,8) | 29,790 | 14,895 | 17,185 | 0.87 | ~29,900 | ~0 | 0.2 M steps |
| 10 | (5,10) | 90,068 | 45,034 | 51,042 | 0.88 | ~88,800 | <0 | |

Cells with need/N_h < 0.7 but huge orders (millions to billions: (13,8), (15,8), (13–16,9), (10,10), (12–16,10)) are
weak relative to the heuristic but out of reach of BFS-based search and of exact checking in this session.
D = 7 with Δ ≥ 9 and D = 5 with Δ ≥ 10 are strong (need/N_h ≥ 1.1): the Loz lifts there are already better than
random Haar graphs; skip. (D = 5, Δ = 6 is the D = 5 agent's.)

## 4. Results so far (all bigcheck VALID: BFS from every vertex, exact diameter)

| cell | table (2013) | ours | group G (order N; graph has 2N vertices) | search time | files |
|---|---|---|---|---|---|
| (7,8) | 80,940 | **82,992** | SL(2,13) × Z₁₉ (41,496) | 147 s | records/bipartite_dd/d7D8/ |
| (8,8) | 201,480 | **206,448** | PSL(2,23) × Z₁₇ (103,224) | 8 s | records/bipartite_dd/d8D8/ |
| (9,8) | 449,480 | **453,840** | PGL(2,61) (226,920) | 69 s | records/bipartite_dd/d9D8/ |
| (6,10) | 452,032 | **461,472** | PSL(2,23) × Z₃₈ (230,736) | 36 s | records/bipartite_dd/d6D10/ |
| (8,9) | 1,091,232 | **1,092,960** | SL(2,23) × Z₄₅ (546,480) | 50 s | records/bipartite_dd/d8D9/ (bigcheck 30 min) |

Failed so far (best uncovered count): (7,9) PSL(2,29) × Z₁₇, N = 207,060: 6 in 600 s; (8,8) PSL(2,23) × Z₂₁,
N = 127,512: 31 in 257 s; (7,8) SL(2,13) × Z₂₁, N = 45,864: 6 in 600 s; (7,10) PSL(2,23) × Z₁₆₄, N = 995,808
(need > 993,690): 2 in 900 s (6 evaluations/s; a 2M-vertex graph would also need ~100 min of bigcheck).

Observed threshold: at even D every attempt with (table/2)/N_h ≤ 0.80 succeeded within 2.5 min; 0.89 and 0.96 failed.
At odd D, 0.82 failed.

**Diameter criterion at even D (used for the search; easy remark).** diam H(G,S) ≤ 2k iff every g ∈ G is an
alternating product s₁s₂⁻¹s₃⋯s₂ⱼ₊₁ with j ≤ k−1. Proof: this says every (g,B) is within 2k−1 of (e,A); inverting
the words, every (g,A) is within 2k−1 of (e,B); right multiplication is transitive on each side, so every vertex is
within 2k−1 of the whole other side, and then two vertices of one side are within 2k via a neighbour. So at even D
there is one covering condition (words of length ≤ D−1), at odd D two (the D = 5 lemma, research/d5/REPORT.md).

**Novelty.** Haar graphs (= lifts of the Δ-dipole) and voltage lifts are standard; Loz–Pérez-Rosés–Pineda-Villavicencio
built many 2013 table entries from lifts. New: the graphs (non-abelian matrix groups of order 4·10⁴–2·10⁵, annealing
with targeted moves: pick an uncovered u, a random walk from the start and one from u, and set the new generator to
join their ends), the heuristic ranking, and the observation that the D = 8 column is weak (table/2 is only 10–13%
of the word bound W). These are single computer constructions, not a family theorem, so there is no REPORT.md
theorem; nothing here uses Delorme 1985 / Delorme–Farhi 1984 / Araujo-Pardo–López.

## 5. Order of work this session

1. (7,8) over groups of order 41–48K (SL(2,13)×Z₁₉ = 41,496 first), push N up after the first success.
2. (8,8) over PSL(2,59) (102,660), SL(2,37)×Z₂ (101,232), PSL(2,23)×Z₁₇ (103,224).
3. If time: (7,9), (9,8).

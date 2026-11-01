# c6c-h12 (handsoff-108): double-coset families with h = 12 in PGL(2,193)

Worker c6c-h12 (relaunch of slot c6, card at the end of ../cards.md). Target: a bipartite degree-10 graph X(G,H,D),
G = PGL(2,193) (|G| = 7,188,864), |H| = 12, N = |G|/12 = 599,072 per side, 2N = 1,198,144 > 1,176,480.
Verdict: no family reaches small cost. Best exact minimum over ALL degree-10 double-coset sets of all three
order-12 subgroups: C = 501 plain (A4). No cost 0, no record, no CLAIM.

## Card correction (read first)

The card says "Degree 10 needs ONE regular double coset". That cannot hold with |H| = 12. A double coset H z H has
c = |HzH|/|H| = 12/k left cosets, k = |H ∩ z H z^-1| in {1,2,3,4,6,12}, so c is in {12,6,4,3,2,1}. A regular
double coset (c = 12) gives degree 12, too many. Degree 10 needs a SET D of double cosets with c-values summing to 10,
so every double coset in D has k >= 2 (non-regular). c5b found such families 3-10x worse than regular ones. I scanned
every such set exactly. (A two-subgroup version, H of order 12 against K of order 10, gives biregular degrees 10/12,
which the card does not allow.)

## Subgroups of order 12 in PGL(2,193) (generators from mkgens.py, closure checked)

- C12 = <(49,0,0,1)>: DCs with c < 12 lie in N(T) (order 384, 32 cosets of H). Every degree-10 set generates a subgroup
  of N(T), so the graph is disconnected. Confirmed: sample of 2 sets, uBA = uAA = uBB = 599,040 (64-vertex component).
- D6 square reflection: H = <(85,0,0,1), (0,1,2,0)>. DCs: c12 49,795; c6 248; c3 4; c2 15; c1 2.
- D6 nonsquare reflection: H = <(85,0,0,1), (0,1,5,0)>. DCs: c12 49,824; c6 192; c2 15; c1 2.
- A4 = <(0,1,192,0), (81,1,112,1)>. DCs: c12 49,857; c6 47; c4 126; c1 2.
  (Counts from `exh12 ... info`; the D6 nonsquare counts equal the c5b J header.)

## Code

- exh12.c (built to exh12): c6b-exhaust/exh.c generalised to any H of order <= 16 and any union D of double cosets with
  c-sum = DEG = 10. Neighbour lists are de-duplicated per double coset, so every graph is simple of degree 10
  (`check` mode). Costs: C = uBA + uAA + uBB (plain vertices), as in c6b.
- Symmetry: D -> D^-1 and D -> nDn^-1 (n in N_PGL(H), order 24 here) act on DC ids (group of order 4). Canonical set =
  smallest image; class weight = number of distinct images. Sum of weights = number of sets (checked against `info`).
- exh12v.c / exh12v = exh12.c plus a `dcof` mode (matrix -> DC id), used by xval.py. Same results.
- run_all.sh (A4, D6 nonsquare, D6 square; the last one stopped and re-run), run_d6sq.sh and run_d6sq622.sh (D6 square
  by partition, then 6+2+2), summ12.py FAMILY (summaries), xval.py (cross-check), mkgens.py (subgroups).
- Partition sizes and totals: `exh12 ... info`.

## Validation

- K family (PSL(2,229), D5, c6b's H): zcost for the 5 best c6b members gives uBA/uAA/uBB exactly
  (4/0/0, 33/0/0, 37/0/0, 41/0/0, 42/0/0). DC counts: 59,985 regular, 113 c5, 11 c2, 1 c1.
- Multi-DC sets: `check` (symmetric adjacency, no repeated neighbours) on a 5+5 and a 2+2+2+2+2 member of K: clean.
- Independent cross-check of multi-DC members against c5b's cscreen (its J run: PGL(2,193), D6 nonsquare, spec
  6,2,2): 4 of 4 members reproduce exactly (cand 0 7082/0/0, cand 1 4575/0/0, cand 2 4772/4/4, cand 3 3764/0/0), xval.py.

## Results: exact scans of every degree-10 set (A-root for all classes; B-root where needed)

Card asked for 100-set samples and then a full scan of the best. The full scans were affordable (they are exact), so
they replace the samples. Medians are over sets (weighted by class size). "P" = uBA + uAA (lower bound of C).

| family | sets | classes | exact min C (plain) | family min | median P (plain) | per unit of 12 |
|---|---|---|---|---|---|---|
| A4 | 13,797 (6+4 5,922; 4+4+1+1 7,875) | 6,016 | 501 (6+4) | 501 (exact) | 49,072 | 4,089 |
| D6 nonsquare | 27,408 (6+2+2 20,160; 6+2+1+1 2,880; 2^5 3,003; 2^4+1+1 1,365) | 15,888 | 1,266 (6+2+2) | 1,266 (exact) | 6,642 | 554 |
| D6 square | 40,480 (6+3+1 1,984; 6+2+2 26,040; 6+2+1+1 3,720; 3+3+3+1 8; 3+3+2+2 630; 3+3+2+1+1 90; 3+2+2+2+1 3,640; 2^5 3,003; 2^4+1+1 1,365) | 20,316 | 900 (6+3+1) | 900 (exact) | 34,273 | 2,856 |
| C12 | 64,512,240 (all c1 types) | - | - | disconnected | - | - |

Family minima are exact: every class without an exact C has P >= the family minimum found (A4 and D6 nonsquare:
equal, so they cannot go lower; D6 square: next lower bound 1320 > 900). "disconnected-like" = uBA > 100,000.
Reference: the K family (h = 10, one regular double coset) has min 4 and median 340 plain (34 per unit of 10).

Per partition (median P in plain vertices):
- A4: 6+4 median 599,072 (3,006 of 5,922 sets disconnected-like); 4+4+1+1 median 47,852 (2,307 of 7,875 disconnected-like).
- D6 nonsquare: 6+2+2 median 5,020 (min P 1,266); 6+2+1+1 median 29,818; 2^5 and 2^4+1+1 disconnected (64-vertex components).
- D6 square: 6+3+1 median 264,298 (min C 900); 6+2+2 median 12,834 (min P 1,500); 6+2+1+1 median 38,287;
  3+3+2+2 median 64,188 (min P 9,000); 3+2+2+2+1 median 229,740; 2^5 and 2^4+1+1 disconnected.

Details of the minima (plain units):
- A4 top exact (B-root for P <= 1500 done): C 501 for classes 382.45928 (self-inverse, uBA 501) and 46305.49590
  (uBB 0, uBA 501); next 527 (23673.49953, 380.49872).
- D6 nonsquare top exact (B-root for P <= 2200 done): C 1,266 for 11304.34241.44927 and 11305.34046.48016; next 1464.
- D6 square top exact (B-root for P <= 2200 done): C 900 for 0.37371.49813 and 23617.38750.45261 (uBB 0, uBA 898,
  uAA 2); next 964 (0.33399.49813, 38750.45261.45417), 984, 1090.

Verdict: none of the three h = 12 families gets near 0 (best 501 plain, A4, about 125 times K's min 4). Every set
has non-regular double cosets (k >= 2), and that is consistent with the collapse we see (many sets disconnected,
the rest with uBA in the hundreds or thousands). The K family's regular double coset is the likely reason it is much
better (a hypothesis, not checked). No cost-0 graph on 1,198,144 vertices exists in these three families.

## Files

- out/A4_scanA.tsv, out/D6nsq_scanA.tsv, out/D6sq_scanA.tsv (A lines: key, orbit weight, sym, uBA, uAA, partition);
  out/D6sq_scanB.tsv, out/A4_scanB.tsv (B lines: key, uBB, uBA, uAA); out/*_summary.txt (summ12.py output);
  out/D6sq_sample622.out (an earlier 500-set random sample of D6 square 6+2+2, superseded by the full scan: min 1,689).
- out/progress.log, out/*.log (logs of the runs).

## Scoreboard

- One line: A4 full scan, best exact C = 501 plain (not a record). D6 nonsquare (1266) and D6 square (900) are worse; no line.

## Next steps (not done)

- Nothing from this card can reach cost 0 with h = 12 in PGL(2,193): all three subgroup classes are exhausted and C12
  is disconnected.
- Among primes q < 1000, PGL(2,193) is the only PGL(2,q) with N = |G|/12 in [588,241, 600,000]. (PSL(2,q) has
  N half as big: no prime q in range.) A larger q (N above 600,000) is allowed but outside this card.

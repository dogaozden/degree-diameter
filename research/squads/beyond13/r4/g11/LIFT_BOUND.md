# g11: an exact upper bound for cyclic (Z_n) lifts, and a screen of bases

Files: lbound.c (the bound program, `./lbound EDGEFILE D [seed] [sources]`), mkbases.py (base graphs, regularity,
bipartiteness and girth checks), bases/*.edges (the bases), res/ and res2/ (program output; res2 = all sources).

## 1. Setting

B is a connected base graph with edges oriented, voltage a: E(B) -> Z_n. The lift B x_a Z_n has vertices (v,h),
v in V(B), h in Z_n, and for each base edge e = (v,w) with voltage a_e the lift edges (v,h)-(w,h+a_e). The projection
(v,h) -> v is a covering map. A walk in B has net vector x in Z^E, x_e = (signed number of traversals of e along its
orientation). Write phi(x) = sum_e x_e a_e mod n.

## 2. Lemma (lift distances are voltages of walks)

For s, v in V(B) and D >= 0 let X_v(s,D) be the set of net vectors of all walks s -> v of length <= D in B.

(a) d_lift((s,0),(v,h)) <= D if and only if h is in phi(X_v(s,D)).

Proof. A walk in the lift starting at (s,0) projects to a walk in B of the same length from s to v. Conversely each
walk in B from s lifts uniquely to a walk in the lift from (s,0). Induction on the walk length gives that the lift
endpoint is (v, phi(x)), since each traversal of e in its orientation adds a_e and each traversal against it subtracts
a_e. So the lift walks of length <= D from (s,0) end at exactly the points (v, phi(x)) with x in X_v(s,D).

(b) Backtracking adds nothing. Deleting an adjacent pair e e^{-1} from a walk keeps its endpoints and its net vector and
shortens it by 2. Hence X_v(s,D) is also the set of net vectors of nonbacktracking walks of length <= D. For bipartite
B with colouring c, every walk s -> v has length = c(s)+c(v) (mod 2), so the parity condition ("walks of the right
parity") is automatic and adds nothing. Walks shorter than D are included, since we take all lengths <= D.

(c) Translation. (v,h) -> (v,h+t) is an automorphism of the lift. So d((s,h),(v,h')) = d((s,0),(v,h'-h)), and the lift
has diameter <= D if and only if for every s and v, phi(X_v(s,D)) = Z_n.

Theorem. If the Z_n lift of B with voltages a has diameter <= D, then for all s, v in V(B)

    n <= W_v(s,D) := |X_v(s,D)|,

the number of distinct net traversal vectors of walks s -> v of length <= D. Hence

    n <= n_max(B,D) := min over s, v of W_v(s,D),     N = b n <= b * n_max(B,D)   (b = |V(B)|).

Proof. By (a) and (c), phi must map X_v(s,D) onto Z_n. A map from a set onto Z_n has at least n preimage classes, so
|X_v(s,D)| >= n. (Lifts with repeated net vectors only lose; W counts distinct vectors, not walks.)

Remarks. W_v(s,D) = W_s(v,D), since reversing a walk negates its net vector. Distinct walks can share a net vector
(two different walks whose difference is a closed walk with zero net vector, e.g. commuting short cycles); this is why W is
below the number of walks (first collisions at length 10 for GP(10,3), girth 6). The bound is
exact as an upper bound on n for a fixed base: any Z_n lift of B with n > n_max cannot have diameter <= D, for any
choice of voltages.

## 3. Computation

lbound.c enumerates all nonbacktracking walks of length <= D from each source s, records (endpoint, hash of net
vector), where the hash is sum_e x_e r_e mod 2^64 with random 64-bit r_e (so distinct net vectors get distinct hashes
except with probability about 1e-7 for the largest runs), and counts distinct hashes per endpoint. Cross-checks: the
GP(10,3) numbers equal those of r3/f03 (LIFTS.md: 20,258 distinct vectors of length <= 13; per-endpoint min 647,
max 1,356), and a second hash seed gives identical minima.

## 4. Results (n_max = min over all sources s and endpoints v)

Cubic bipartite bases (N_bound = b * n_max). "Found" is the best valid cyclic lift known from earlier rounds.

| base | b | girth | D=13 n_max | N_bound(13) | D=14 n_max | N_bound(14) |
|---|---|---|---|---|---|---|
| GP(8,3) (Mobius-Kantor) | 16 | 6 | 709 | 11,344 | 1,323 | 21,168 |
| Heawood | 14 | 6 | 773 | 10,822 | 1,290 | 18,060 |
| **GP(10,3) (Desargues)** | 20 | 6 | **647** | 12,940 | **1,197** | 23,940 |
| GP(12,5) | 24 | 6 | 571 | 13,704 | 1,093 | 26,232 |
| GP(14,3) | 28 | 6 | 543 | 15,204 | 1,029 | 28,812 |
| GP(14,5) | 28 | 6 | 543 | 15,204 | 1,029 | 28,812 |
| GP(16,3) | 32 | 6 | 463 | 14,816 | 907 | 29,024 |
| GP(16,5) | 32 | 6 | 463 | 14,816 | 907 | 29,024 |
| GP(18,5) | 36 | 8 | 429 | 15,444 | 828 | 29,808 |
| GP(20,3) | 40 | 6 | 337 | 13,480 | 684 | 27,360 |
| GP(20,7) | 40 | 6 | 337 | 13,480 | 684 | 27,360 |
| GP(24,5) | 48 | 8 | 318 | 15,264 | 634 | 30,432 |
| GP(30,7) | 60 | 8 | 250 | 15,000 | 499 | 29,940 |
| Tutte 8-cage | 30 | 8 | 505 | 15,150 | 945 | 28,350 |
| random cubic bip. (rnd10_1) | 20 | 4 | 523 | 10,460 | 963 | 19,260 |
| random cubic bip. (rnd12_0) | 24 | 4 | 519 | 12,456 | 969 | 23,256 |
| random cubic bip. (rnd24_1) | 48 | 4 | 193 | 9,264 | 425 | 20,400 |

Other bases (4-regular, bipartite):

| base | b | girth | D=13 n_max | N_bound(13) | D=14 n_max | N_bound(14) |
|---|---|---|---|---|---|---|
| K4,4 | 8 | 4 | 25,116 | 200,928 | see res2/k44.D14.txt | |
| PG(2,3) Levi graph | 26 | 6 | 50,419 | 1,310,894 | 140,275 | 3,647,150 |
| GQ(3,3) Levi graph (W(3)) | 80 | 8 | 19,441 | 1,555,280 | see res2/gq33_levi.D14.txt | |

Quotient found / n_max (how close the known lifts come to the bound):
- GP(10,3): D=13 valid n=160 (N=3,200, r2/e16): 160/647 = 0.25. D=14 n=280 (N=5,600): 280/1,197 = 0.23.
- PG(2,3): D=13 valid n=4,600 (N=119,600; APSP-verified in r3/f04): 4,600/50,419 = 0.09.
- GQ(3,3): no valid lift known. Best attempted n=2,400 at D=13 (N=192,000, cost 1,534) gives 2,400/19,441 = 0.12.
  The D=14 attempt n=6,100 (N=488,000, cost 1,330 at start) gives 6,100/57,511 = 0.11.

## 5. Reading

- The bound is loose. For GP(10,3) it allows n up to 647 at D=13, while random and searched voltages fail above about
  160. The gap comes from voltage coincidences (commuting cycles) and the random-covering behaviour the model in
  r3/f03 describes; the bound does not see them. So n_max is a hard ceiling, not a prediction.
- For K4,4 (Delta = 4) the ceiling is N <= 200,928 at D=13. This does not rule out 190k, but the r3 note already
  gives K4,4 lifts a model value near 3e4. The bound alone cannot close that gap.
- Among cubic bipartite bases, N_bound at D=13 is 9k-15.5k for every base checked. Girth-8 bases (GP(18,5), GP(24,5),
  GP(30,7), Tutte 8-cage) have N_bound 15,000-15,444, above GP(10,3) (12,940). This is a bound, not an estimate, so
  it is only a hint: the quotient for GP(10,3) is 0.25, and no girth-8 base has been searched yet.

## 6. Next

Lift search (cyclic voltages, n in 100-120) on GP(18,5) (b = 36, girth 8, N_bound 15,444 at D=13). The bound
quotient of GP(10,3) predicts about n = 105-110 (N about 3,800-4,000). If that is too easy, go to n = 120-125.

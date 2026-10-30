# d75-raise: the (7,5) cell above 1,200

Job "d75-raise" (Opus cloud session, Oct 30 2026, from 14:08 UTC). Goal: a bipartite graph of maximum degree 7 and
diameter 5 on more than 1,200 vertices (our record 1,200 = Haar graph of SL(2,5) x C5; table 1,134).

Status: in progress, see the end of this file.

## Tools (src/)

| file | what it does | calibration |
|---|---|---|
| `export.g` | GAP: SmallGroup(N,ID) (or any group G) as a multiplication table (identity 0) + inverses; classes of automorphisms of prime order 2, 3, 5, 7 with centralizer generators; with `INVS` the involution classes and the index-2 subgroups. | |
| `haar75.c` | Haar graphs H(G,S), valency 7: `exh` enumerates every S invariant under an automorphism of prime order (types f fixed + m orbits: p = 2 (1,3), (3,2), (5,1); p = 3 (1,2), (4,1); p = 5 (2,1); p = 7 (0,1)), first orbit up to the centralizer; `sa` plain annealing. Fast rejection: z is in X X iff x^-1 z is in X for some x in X, targets in move-to-front order (0.2 us per set). Types with more than MAXEV sets are cut (CAPPED in the log). | SmallGroup(600,54) = SL(2,5) x C5: the 1,200 graph (4 sets) in 0.1 s, all types in 14 s; apsp VALID |
| `bic75.c` | bi-coset graphs B(G;H,K;D), \|H\| = \|K\| = 2, valency 7: every union D of (K,H)-double cosets, for every pair of non-central involution classes; same fast rejection on X = D^-1 D, Y = D D^-1, plus D X X = G. First double coset up to conjugation by C(h) n C(k). | SmallGroup(1200,475): 720 unions found (the 1,200 graph), 2 CPU-min; apsp VALID |
| `lift22.c` | regular lifts of the 4-vertex base [[a,b],[b,a]] by a group (set-product cost, 6 conditions), annealing or `TABU=1`. | (5,5): the 384-vertex lifts of SmallGroup(96,51) in < 1 s (apsp VALID) |
| `run1.sh`, `sweep1.sh`, `brun1.sh`, `lscreen.sh`, `stop_sweep.sh` | drivers (one group; a list in parallel; bi-coset; lift screen; stop). | |
| `list_groups.g` | non-abelian SmallGroups of a range of orders with their number of involution classes / involutions. | |

Check: `src/apsp` is research/lifts/coordinator_check/apsp.c (all-pairs BFS, no symmetry assumed).

## Results

(filled in as the job runs)

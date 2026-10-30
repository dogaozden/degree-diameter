# selfdual-d5: self-dual (bipartite Cayley) Haar graphs in other diameter-5 cells

Job "selfdual-d5" (Opus cloud session, Oct 30 2026, from 20:35 UTC). Method from `../d75-raise/README.md` (the (7,5)
1,312 record): if S is a union of orbits of psi(x) = c^-1 beta(x)^-1 for an extension G^ = G u G t of G
(t^2 = c, t x t^-1 = beta(x)), then H(G,S) = Cay(G^, tS) is vertex-transitive and only X X = G (X = S^-1 S) has to
be checked. Work in progress; see the status section at the end.

## Tools (src/)

| file | what it does | calibration |
|---|---|---|
| `export_sd.g` | GAP: SmallGroup(N,ID) as a multiplication table + inverses; `ALPHA 1` (identity) and `ALPHA 2` (each class of involutions of Aut(G)) with centralizer generators (split cosets, c = e); `EXT c` for every Aut(G)-class of pairs (beta, c), c <> e, beta(c) = c, beta^2 = conjugation by c, with the stabilizer (non-split cosets: needed when T has no involution, K even). | |
| `sdk.c` | valency K (env K): ALPHA records: S = e + (f-1) psi-fixed + m psi-2-orbits, f + 2m = K, f >= 1, f = K mod 2; EXT records (K even): S = {e, c^-1} + K/2 - 1 further 2-orbits. First free orbit (or fixed element when m = 0) up to the stabilizer. Fast rejection as in haar75 (move-to-front targets); every set with X X = G gets the full three-condition Haar check. Caps MAXEV, MAXEVF (types with f >= 4); `SAMPLE=1` draws random sets of each type instead. | K = 7 on SmallGroup(656,28): the same 9 sets as haar75 anti (the 1,312 record), all types 36 s (`logs/calib/K7_656_28.out`). K = 6 on SL(2,7) = SmallGroup(336,114): 38 sets, apsp VALID at D = 5 (672 vertices, below the table's 684) |
| `export_hat.g`, `brute.c`, `canon_cmp.py` | independent check: every inverse-closed T of size K in the coset of an index-2 subgroup of a group of order 2n, no normalisation, diameter by BFS; isomorphism classes (nauty-labelg) compared with sdk's | SL(2,7), K = 6: the 4 groups of order 672 containing it give 3,360 hits = 5 classes = sdk's 5 classes. C5 x (C13 : C4) = SmallGroup(260,2): sdk's 7 classes from non-split cosets (EXT) = the classes of the 18,720 brute hits on the two non-split groups 520_5, 520_6 (no involution in the coset); no brute class outside sdk's (`logs/calib/brute_vs_sdk.txt`) |
| `cover.py` | coverage table of a sweep log | |
| `run1.sh`, `sweep.sh` | drivers: one group (export + sdk, one line in `logs/K$K/sweep.txt`), a list in parallel | |
| `list_groups.g` | non-abelian SmallGroups of a range of orders with their numbers of involution classes and involutions | |

Check of every hit: research/lifts/coordinator_check/apsp.c (`src/apsp`), VALID at D = 5 and INVALID at D = 4.

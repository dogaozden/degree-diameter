# Referee checks for research/synthetic/D7_THEOREMS.md

Job "referee-d7thm", 30 October 2026. Report: `../d7-theorems.md`. Everything here is new code, written from the
statements printed in D7_THEOREMS.md, D7_HEXAGON.md and POLISHED.md §6; nothing imports the note's programs. The only
lab code used is `conics2/typed_build.py`, to rebuild the (18,7) edge list from its solution file (as the earlier
referee did for the D7_HEXAGON records); that edge list is then checked with `bfsd.c` below.

| file | what it checks | output |
|---|---|---|
| `nums.py` | identities of §0–1; Theorem 2.2 ($f_j$, $g_j=f_{2k-j}$, minima) for $k\le40$; the ranges of $(\ast)$; Theorem 2.1 on all labelled regular tournaments with 3, 5, 7 levels and every typing, and on 20,000 random ones with 9–15 levels; the best layout over all of them equals the alternating one; the build layouts of §2; $F_k$ against the slot formulas for every prime power $q\le200$, $1\le k\le q-1$ | `nums.out` |
| `builds.py` | the 12 make logs of job conics-2 (branch `claude/conics-2-diameter-7-ic0oat`): set sizes, slot vectors, hub counts and $n$ against the formulas of §2 | `builds.out` |
| `certs.py` | every line of `d7thm/hubopt.out` (590 certificates) against Lemmas 4.1, 4.2 and the slot counts; the thresholds $q_k$; Lemma 4.1 alone for every prime power $200<q\le2\cdot10^5$, $2\le k\le12$; the numbers of the proof of Theorem 4.4(a) | `certs.out`, `certs.json` |
| `mysearch.py` | own search (sums of blow-ups and one pendant-tree part) for every $(q,k)$ below $q_k$ | `mysearch.out` |
| `table52.py` | the table of §5.2 (best $(q,k)$ per cell, $F_k$, status, proved value) and the random-hub-graph table of §4 | `table52.out` |
| `hexlib.py`, `t_hex.py` | own $\mathrm{GF}(q)$ and own $H(q)$ from the coordinates and Tits' equations; distance profile | `t_hex.log` |
| `build31.py` | rebuild of the graph of Theorem 3.1 from the printed definitions (Hermitian spread, $\nu$, $G$, $F$, $W$, $S_0$, elliptic quadric section, $\sigma$ as in D7_HEXAGON Prop. 5.2, alternating layout, hubs on random free slots); asserts Lemma 1.2, Theorem 1.4(a)–(c), Lemma 1.6, Theorem 1.7, Corollary 1.8, Proposition 1.9, Theorem 2.2 on the way | `build_small.log` ($q=3,4,5$; controls), `build_large.log` ($q=7,8$) |
| `hubtests.py` | Lemma 4.1 (random blow-ups of $H(2)$, $H(3)$), Lemma 4.2 (a four-part sum with a pendant-tree part last), Lemma 4.3, a negative control (pendant-tree part first), the note's $H(7)+H(7)$ and the $(16,2)$ certificate $H(8)+H(7)+H(5)+H(4)^{\times2}+H(4)^{\times2}$ | `hubtests.log` |
| `hubfiles.py` | the hub graphs stored in the (18,7), (17,7) and (20,7) solution files and the PSL(2,29) hub graph of job conics | `hubfiles.log` |
| `dualseg288.py` | §1.3 Remark (ii): the 288-line set of card conics2-r1/c8 is a dual segment set, and the card's geometry is $H(4)$ (points distance-2 regular, compared with own $H(4)$) | `dualseg288.log` |
| `bfsd.c` | bit-parallel BFS (64 sources per word, OpenMP): simple, bipartite, degrees, largest same-colour and different-colour distance, pairs beyond $D$; optional source range or random sample | all `.log` files |
| `d18_check.log` | the (18,7) graph rebuilt from `d18D7_hex13_typedwhisk_h7h7_n7318644.sol`: sha256, `bfsd` from all 78,432 hubs and from 6,400 random level vertices | |

Commands (from this directory; `SP` a scratch directory; the note's branch checked out in `$CELLS`, the conics-2
branch in `$C2`):

    gcc -O3 -march=native -fopenmp -o bfsd bfsd.c
    python3 nums.py > nums.out
    python3 builds.py $C2/research/synthetic/conics2 > builds.out
    python3 certs.py $CELLS/research/synthetic/d7thm/hubopt.out > certs.out
    python3 mysearch.py > mysearch.out; python3 table52.py > table52.out
    python3 t_hex.py 2 3 4 5 7 > t_hex.log
    python3 build31.py 5 2 H2 $SP/g.edges 1 && ./bfsd $SP/g.edges 7        # likewise 3 2 edge, 4 2 c12, 4 3 edge,
                                                                          # 5 3 c12, 5 4 edge, 7 2 H4, 7 3 H3, 8 2 H4+H2
    python3 build31.py 5 2 H2 $SP/g0.edges 1 nohubgraph && ./bfsd $SP/g0.edges 7   # control: must fail
    python3 hubtests.py h7h7 $SP/h.edges && ./bfsd $SP/h.edges 6          # likewise blow2 blow3 sum tree treefirst cert16
    python3 $C2/research/synthetic/conics2/typed_build.py build $CELLS/research/p4/d6/hex/hex_q13.bin \
        $CELLS/research/frontier/sols/d18D7_hex13_typedwhisk_h7h7_n7318644.sol $SP/d18.edges
    ./bfsd $SP/d18.edges 7 7240212 7318644; ./bfsd $SP/d18.edges 7 0 7240212 6400

For a hub graph only the line "same-colour ordered pairs at distance > 6" matters (different colours may be at
distance 7); for a whole graph the "RESULT" line.

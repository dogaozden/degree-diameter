# d7thm: programs of research/synthetic/D7_THEOREMS.md

Job "thm-conics", 29 October 2026. Each script writes the `.out` file of the same name.

| file | what | section |
|---|---|---|
| `slots.py` → `slots.out` | best typings of the rotational tournament (k <= 8), all regular tournaments on 5 and 7 levels, SAT on 9-13 levels (`pip install python-sat`) | 2 |
| `hubcap_lib.py` | shared helpers: prime powers, K0(s), slot counts of Theorem 2.2, the pendant-tree feasibility (Lemma 4.3) | 4 |
| `hubcap.py` → `hubcap.out` | Lemma 4.1 alone for every prime power q <= 2*10^5, k <= 12; the inequalities of Theorem 4.4(a) | 4 |
| `hubopt.py` → `hubopt.out` | Lemma 4.2 sums: for every (q, k), q <= 200, k <= 12, the largest hub counts <= the slots that the search finds, with verified certificates (pendant-tree parameters printed); Theorem 4.4(b) | 4 |
| `hubsum.py` → `hubsum.out` | the first-found search used in an earlier draft (superseded by hubopt.py) | 4 |
| `build_cert.py` | builds the hub graph of a hubopt certificate as an edge list (needs hex_q{s}.bin from research/d10D7/hexgen2.c); `--typed` writes the hub-file format of conics2/typed_build.py | 4 |
| `d18D7/` | the (18,7) graph with the H(7)+H(7) hub graph: builder log, level-part comparison, check from every hub; solution file research/frontier/sols/d18D7_hex13_typedwhisk_h7h7_n7318644.sol | 5 |
| `hgcheck.c` | standalone hub-graph check (same-colour distances <= 6, degrees, no repeated edges); modes `sol`, `edges`, `rand [repair]`, `haar` | 4 |
| `hgcheck_lab.out` | the lab's stored hub graphs (solution files of branch claude/conics-2-diameter-7-ic0oat) re-checked | 4 |
| `hgrun.py` → `hgrun.out`, `gapresults.py` | random hub graphs at the slot counts for the (q, k) below q_k | 4 |
| `cert_checks.out` | certificate graphs built and checked: (16,2), (17,2), (23,3) | 4 |
| `cells.py` → `cells.out` | formulas against all 15 built graphs; closed forms of Corollary 3.2 | 3, 5 |
| `table.py` → `table.out`, `table.md` | the cells (Delta, 7), Delta = 14..26 | 5 |
| `make_pdf.sh` | D7_THEOREMS.md -> .tex (pandoc) -> .pdf (tectonic); run from research/synthetic/ | |

Commands (from this directory):

    python3 slots.py; python3 hubcap.py; python3 hubsum.py 200; python3 cells.py
    cc -O2 -fopenmp -o hgcheck hgcheck.c
    ./hgcheck sol ../../frontier/sols/d19D7_hex16_typedwhisk_nu0_n11316940.sol 14    # (solution files on the conics-2 branch)
    (cd /tmp && mkdir -p hex && cc -O2 -o hexgen2 .../research/d10D7/hexgen2.c && for s in 2 3 4 5 7 8 9 11; do ./hexgen2 $s; done)
    python3 build_cert.py 16 2 /tmp/hex cert.txt 1 && ./hgcheck edges cert.txt 14
    python3 build_cert.py 13 4 /tmp/hex hub18.txt 1 --typed      # the (18,7) hub graph H(7)+H(7)
    python3 .../conics2/typed_build.py build research/p4/d6/hex/hex_q13.bin research/frontier/sols/d18D7_hex13_typedwhisk_h7h7_n7318644.sol d18.edges
    OMP_NUM_THREADS=3 python3 hgrun.py; python3 gapresults.py; python3 table.py

# lean-all: status of every record without a Lean ✓ in README.md

Started 2026-10-25 (cloud session, branch `claude/lean-all-jvj7b0`). Lean files are in `lean/BipartiteDD/LeanAll/`;
axioms in `lean/BipartiteDD/LeanAll/Axioms.out.txt` (only propext, Classical.choice, Quot.sound).

| cell | record | construction | status | theorem / file |
|---|---:|---|---|---|
| (11,6) | 148,944 | Theorem D, q = 9, m = 2 | **done** | `nb_11_6`, LeanAll/D6.lean |
| (13,6) | 388,972 | Theorem D, q = 11, m = 2 | **done** | `nb_13_6`, LeanAll/D6.lean |
| (15,6) | 870,440 | Theorem D, q = 13, m = 2 | **done** | `nb_15_6`, LeanAll/D6.lean |
| (16,6) | 940,846 | Theorem D, q = 13, m = 3 | **done** | `nb_16_6`, LeanAll/D6.lean |
| (8,5) | 2,048 | route-chart lift | **done** | `nb_8_5_2048`, LeanAll/D8D5 (orbit BFS v1, 64 sources) |
| (4,7) | 864 | Haar / Cayley-type (Heis(3) × C16) | **done** | `nb_4_7_864`, LeanAll/D4D7 (orbit BFS v1, 2 sources) |
| (10,5) | 4,800 | GQ doubled-matching lift, W(7), Z6 | **done** | `nb_10_5_4800`, LeanAll/D10D5 (orbit BFS v2, 800 sources) |
| (11,5) | 7,020 | GQ lift, W(8) | **done** | `nb_11_5_7020`, LeanAll/D11D5 (1,170 sources) |
| (12,5) | 9,840 | GQ lift, W(9) | **done** | `nb_12_5_9840`, LeanAll/D12D5 (1,640 sources) |
| (13,5) | 11,486 | unit design | **done** | `nb_13_5_11486`, LeanAll/D13D5 (1,644 sources) |
| (14,5) | 17,568 | GQ lift, W(11) | building (staged BFS) | LeanAll/D14D5 |
| (15,5) | 20,736 | route-chart lift | building (staged BFS) | LeanAll/D15D5 |
| (16,5) | 33,792 | route-chart lift | building (staged BFS) | LeanAll/D16D5 |
| (6,8) | 31,680 | Haar, PSL(2,11) × Z24 | building (staged BFS, 2 sources) | LeanAll/D6D8 |
| (7,7) … (15,7) | 23,580 … 2,484,720 | hexagon + hubs | todo | |
| (8,9) | 1,326,960 | Haar, SL(2,19) × Z97 | **done** | `nb_8_9_1326960`, LeanAll/HaarD8D9 (packed batch checks, 720 batches) |
| (8,10) | 7,818,096 | Haar, SL(2,67) × Z13 | building | LeanAll/HaarD8D10 |
| (10,9) | 8,003,856 | Haar, SL(2,83) × Z7 | building | LeanAll/HaarD10D9 |
| (11,9) | 16,792,080 | Haar, SL(2,61) × Z37 | building | LeanAll/HaarD11D9 |
| (15,8) | 18,128,880 | Haar, SL(2,109) × Z7 | building | LeanAll/HaarD15D8 |
| other D = 8–10 Haar cells | 2.3M … 1.3B | Haar (SL, PSL, products) | todo | |

The D = 6 cells are instances of the Theorem D family already in Lean (`HexagonD.theoremD`, any finite field of odd
characteristic): the vertex formula 2(q+1)(q⁴+q²+1) + (m−1)(q⁴+2q³+q²+2q+2 + m(q³+q+2) + m²) + (m−1)(q⁴−q²) gives
exactly the four record values.

## Method for the graphs checked one by one (`LeanAll/Orbit.lean`, `LeanAll/Orbit2.lean`)

A bitmask search from a block of sources (bit j of a vertex's mask = source j is within r steps) is run by the kernel
(`decide +kernel`). Automorphisms cut the sources to one per orbit: nauty (`dreadnaut`, built from source) finds
generators (`auts.py`); the kernel checks each is a bijection that maps neighbour lists onto neighbour lists
(`permOK`), and that every vertex outside the representatives is moved below itself by some generator (`orbitOK`),
so by induction every vertex has the eccentricity of a representative. `gen_orbit2.py` renumbers the vertices
(representatives first), writes the graph as balanced trees of literals and the check modules. For larger graphs
(`--staged`) the masks of every radius are written as data and each radius step is its own module.

Kernel lessons (benchmarks in the session): structural recursion over long ranges is quadratic in the kernel (use
`Nat.rec` with the index taken from the recursor's own literal argument); `List.foldl`/`all`/`any` through `brecOn`
dominate small loops (use `List.rec`); a tree lookup costs about 70 µs per level; each kernel step allocates about
0.7 kB that stays cached until the declaration ends, so memory, not time, sets the module size.

## Method for the Haar cells (`LeanAll/Swar.lean`, `HaarSwar.lean`, `HaarSL.lean`)

The diameter of a Haar graph of `G = SL(2,p) × Z_n` follows from a cover of `G` by words of `D - 1` letters (existing
lemmas `haar_ediam_le_odd/even`). The elements are numbered so that batch `b` (fixed `a, c` of the matrix, or fixed `a`
when `c = 0`) holds `p n` consecutive elements, slot `d n + z`. A batch check (`batchOK`) multiplies all `p n` slot
words at once with `40`-bit packed fields: the certificate number holds, per slot, the `D - 1` digits of its word
(4 bits each); the kernel extracts each digit, builds selection masks, multiplies by the selected letter, reduces mod
`p` (approximate Barrett step, one conditional subtraction, and a check that every field is below `p`) and mod `n`,
and finally compares with the slot targets (`a`, `c`, the ramps `d` and `z`). `batch_sound` proves that a passing
batch gives, for every slot, a word whose product has those entries; `cover_of_batches` turns all batches into a cover
of `G` (the determinant fixes the fourth entry). Certificates come from `haarcert.c` (BFS over the group, every word
re-evaluated). A batch of about 2,000 slots takes about 0.3 s in the kernel.

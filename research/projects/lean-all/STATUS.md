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
| (14,5) | 17,568 | GQ lift, W(11) | **done** | `nb_14_5_17568`, LeanAll/D14D5 (staged orbit BFS, 2,928 sources) |
| (15,5) | 20,736 | route-chart lift | **done** | `nb_15_5_20736`, LeanAll/D15D5 (staged orbit BFS) |
| (16,5) | 33,792 | route-chart lift | **done** | `nb_16_5_33792`, LeanAll/D16D5 (staged orbit BFS) |
| (6,8) | 31,680 | Haar, PSL(2,11) × Z24 | **done** | `nb_6_8_31680`, LeanAll/D6D8 (staged orbit BFS, 2 sources) |
| (8,9) | 1,326,960 | Haar, SL(2,19) × Z97 | **done** | `nb_8_9_1326960`, LeanAll/HaarD8D9 (720 batches × 2) |
| (11,8) | 2,258,520 | Haar, PSL(2,59) × Z11 | **done** | `nb_11_8_2258520`, LeanAll/HaarD11D8 (1,740 sign-normalised batches) |
| (8,10) | 7,818,096 | Haar, SL(2,67) × Z13 | **done** | `nb_8_10_7818096`, LeanAll/HaarD8D10 (4,488 batches) |
| (10,9) | 8,003,856 | Haar, SL(2,83) × Z7 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_10_9_8003856`, LeanAll/HaarD10D9 (6,888 batches × 2) |
| (11,9) | 16,792,080 | Haar, SL(2,61) × Z37 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_11_9_16792080`, LeanAll/HaarD11D9 (3,720 batches × 2) |
| (15,8) | 18,128,880 | Haar, SL(2,109) × Z7 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_15_8_18128880`, LeanAll/HaarD15D8 (11,880 batches) |
| (9,10) | 23,975,280 | Haar, PSL(2,71) × Z67 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_9_10_23975280`, LeanAll/HaarD9D10 (2,520 batches) |
| (12,9) | 34,026,720 | Haar, SL(2,41) × Z247 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_12_9_34026720`, LeanAll/HaarD12D9 (1,680 batches × 2) |
| (10,10) | 60,141,120 | Haar, SL(2,79) × Z61 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_10_10_60141120`, LeanAll/HaarD10D10 (6,240 batches) |
| (13,9) | 67,742,688 | Haar, SL(2,103) × Z31 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_13_9_67742688`, LeanAll/HaarD13D9 (10,608 batches × 2) |
| (14,9) | 116,068,656 | Haar, SL(2,67) × Z193 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_14_9_116068656`, LeanAll/HaarD14D9 (4,488 batches × 2) |
| (13,8) | 6,999,552 | Haar, SL(2,7) × SL(2,7) × Z31 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_13_8_6999552`, LeanAll/HaarD13D8 (16,128 batches, HaarProd) |
| (9,9) | 3,499,776 | Haar, PSL(2,7) × SL(2,7) × Z31 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_9_9_3499776`, LeanAll/HaarD9D9 (8,064 batches × 2, HaarProd) |
| (7,10) | 2,237,760 | Haar, PSL(2,5) × SL(2,8) × Z37 | **done** | `nb_7_10_2237760`, LeanAll/HaarD7D10 (GF(8) batches, HaarGF8) |
| (12,10) | 325,832,976 | Haar, SL(2,107) × Z133 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_12_10_325832976`, LeanAll/HaarD12D10 (11,448 batches, streamed) |
| (15,9) | 208,029,120 | Haar, SL(2,79) × Z211 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_15_9_208029120`, LeanAll/HaarD15D9 (6,240 batches × 2, streamed) |
| (16,9) | 337,394,400 | Haar, SL(2,151) × Z49 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_16_9_337394400`, LeanAll/HaarD16D9 (22,800 batches × 2, streamed) |
| (13,10) | 677,714,400 | Haar, SL(2,199) × Z43 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_13_10_677714400`, LeanAll/HaarD13D10 (39,600 batches, streamed) |
| (14,10) | 1,326,627,120 | Haar, SL(2,139) × Z247 | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_14_10_1326627120`, LeanAll/HaarD14D10 (19,320 batches, streamed, blockwise ramps) |
| (5,8) | 9,760 | Haar, Z61 ⋊ Z80 (record added during this session) | **done** | `nb_5_8_9760`, LeanAll/MetaD5D8 (per-element word checks, gen_meta.py) |
| (5,9) | 29,756 | Haar, Z346 ⋊ Z43 (added during this session) | **done** | `nb_5_9_29756`, LeanAll/MetaD5D9 |
| (11,10) | 148,729,680 | Haar, PSL(2,89) × Z211 (added during this session) | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_11_10_148729680`, LeanAll/HaarD11D10 (3,960 batches, streamed) |
| (8,9) | 1,341,600 | Haar, SL(2,25) × Z43 (added during this session; replaces 1,326,960) | **done** | `nb_8_9_1341600`, LeanAll/HaarD8D9b (15,600 batches × 2, GF25, HaarGF25) |
| (9,8) | 546,720 | Haar, SL(2,16) × Z67 (added during this session; Lean ✓ is for 540,360) | **done** | `nb_9_8_546720`, LeanAll/HaarD9D8 (4,080 batches, GF16, HaarGF16) |
| (15,10) | 2,467,618,800 | Haar, SL(2,149) × Z373 (added during this session) | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_15_10_2467618800`, LeanAll/HaarD15D10 (22,200 batches in 11,100 modules, gen_haarsl2.py, streamed; 6.4 h on 4 cores) |
| (16,10) | 4,220,872,800 | Haar, SL(2,151) × Z613 (added during this session) | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_16_10_4220872800`, LeanAll/HaarD16D10 (22,800 batches of 92,563 slots, gen_haarsl2.py, streamed; 13.2 h on 4 cores) |
| (9,5) | 2,758 | Haar, Z197 ⋊ Z7 (raised on master 2026-10-26; Lean before: 2,662) | **done** | `nb_9_5_2758`, LeanAll/MetaD9D5 (gen_meta.py) |
| (13,5) | 11,700 | lift of a generalized quadrangle (raised on master 2026-10-26, was 11,486) | **done** | `nb_13_5_11700`, LeanAll/D13D5b (orbit BFS v2, 1,170 sources) |
| (3,10) | 810 | voltage lift over C3 × He3 (added on master 2026-10-26) | **done** | `nb_3_10_810`, LeanAll/D3D10 (orbit BFS v2, 2 sources) |
| (7,10) | 2,298,240 | Haar, SL(2,7) × PSL(2,19) (raised on master 2026-10-26) | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_7_10_2298240`, LeanAll/HaarD7D10b (as PSL(2,19) × Z1 × SL(2,7): 60,480 batches, HaarProd2.cover_prod_pm with n = 1) |
| (8,10) | 8,043,840 | Haar, PSL(2,7) × PSL(2,19) × Z7 (raised on master 2026-10-26) | **done** (files not committed: cells.txt, axioms_big.txt) | `nb_8_10_8043840`, LeanAll/HaarD8D10b (as PSL(2,19) × Z7 × PSL(2,7): 30,240 batches, HaarProdP.cover_prod_pp) |
| (7,7) … (15,7) | 23,580 … 2,484,720 | hexagon + hubs | not here: the hexagon-family project has a Lean certificate theorem for these (branch `claude/hexagon-family-blvamb`) | |

## Records outside the README table (research/RESULTS.md)

| cell | record | construction | status | theorem / file |
|---|---:|---|---|---|
| (3,11) | 1,320 | voltage lift over SmallGroup(165,1) | **done** | `nb_3_11_1320`, LeanAll/D3D11 (orbit BFS v2, 8 sources) |
| (3,12) | 1,320 | PSL(2,11) Cayley-type graph | **done** | `nb_3_12_1320`, LeanAll/D3D12 (orbit BFS v2, 1 source) |
| (19,3) | 624 | fourth hat, q = 17 | **done** | `nb_19_3_624`, LeanAll/D19D3 (orbit BFS v2, 326 sources) |
| (19,4) | 10,982 | AS17 with clones | **done** | `nb_19_4_10982`, LeanAll/D19D4 (orbit BFS v2, 41 sources; 2 random products of nauty's 582 generators, `randgens.py`) |
| (4,12) | 50,160 | Haar, SL(2,11) × Z19 | **done** | `nb_4_12_50160`, LeanAll/HaarD4D12 (gen_haarsl2.py, 48-bit fields for words of 11 letters) |
| (5,11) | 253,080 | Haar, PSL(2,19) × Z37 | **done** | `nb_5_11_253080`, LeanAll/HaarD5D11 (gen_haarsl.py, 48-bit fields) |
| (5,12) | 912,576 | Haar, PSL(2,97) (n = 1) | **done** | `nb_5_12_912576`, LeanAll/HaarD5D12 (gen_haarsl.py --chain2: HaarPSL2 allows n = 1) |
| (4,11) | 19,152 | Haar, SL(2,8) × Z19 | **done** | `nb_4_11_19152`, LeanAll/HaarD4D11 (GF(8), HaarGF8Z.cover8, gen_haar8.py) |

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

`HaarPSL.lean` does the same for `PSL(2,p) × Z_n` (the quotient of `SL(2,p) × Z_n` by `(-1, 0)`): batches run over
sign-normalised matrices only (`c` in `1 … (p-1)/2`, or `c = 0` and `a` in `1 … (p-1)/2`) and the final comparison
accepts either sign through fieldwise equality masks (`batchOKpm`, `batch_sound_pm`, `cover_of_batches_pm`); the record
forms map words to the quotient (`psl_record_odd/even`).

`HaarProd.lean` handles `SL(2,p) × Z_n × SL(2,q)` and `PSL(2,p) × Z_n × SL(2,q)`. A batch fixes the second matrix and
runs over the slots of the first factor as before; the same certificate is checked twice, once with the first factor's
letters against the ramp targets and once with the second factor's letters (same digits and shifts) against constant
targets (`word_const`, from the general `batch_sound`). The covers of the first factor are restated keeping the
certificate (`cover_of_batches_ex`, `cover_of_batches_pm_ex`).

Generated files (`gen_haarsl.py`, `gen_haarprod.py`): `Defs` (letters, parameters, constants, the batch predicate),
`Bat*` (one theorem per batch, the certificate number is the witness and `decide +kernel` checks it; the module's
range lemma joins the batches by a balanced tree of `range_join`/`range_one` from `LeanAll/Range.lean`, no case
splits), `Cover*` (the range lemmas joined the same way) and `Record`. Cells whose generated files are too large to
commit are listed in `cells.txt` with the command that writes them, and `manifests/<Cell>.sha256` holds the sha256 of
every generated file (the generators and certificate programs are deterministic).

Builds: `poolq.py` runs a queue file (memory budget, barriers between stages, jobs may be appended while it runs;
`!MOD` runs `lean` directly on a module whose imports are built, which saves the lake start-up of about 3 s per job).
Rates seen here: about 3,000–5,000 slots per second per core, depending on the degree and the batch size.

`GF8.lean` and `HaarGF8.lean` give the second factor `SL(2,8)` of the (7,10) cell: `GF8` is `Fin 8` with xor addition
and multiplication modulo `x³ + x + 1` (ring axioms by `decide`); a packed state holds each entry's bits spaced three
apart, so integer products carry nothing between coefficients, and `red8` (fieldwise: parity, then `x³ = x + 1`,
`x⁴ = x² + x`) reduces them; the field-level identity `red1_sp` is checked over all 4,096 cases.

`GF16.lean`/`HaarGF16.lean` do the same over `GF(16)` (spacing four, `x⁴ = x + 1`) for `SL(2,16) × Z67` (9,8): one
batch per matrix and free entry, constant matrix targets, and the `n` slots are the `Z_n` values, checked by the
`HaarSwar` batch over `ZMod 2` with identity letters (`cover16`). `GF25.lean`/`HaarGF25.lean` give `GF(25) =
F₅[x]/(x² + 2)` for `SL(2,25) × Z43` (8,9): an element `c₀ + c₁ x` is the code `c₀ + 128 c₁`, so a sum of two
integer products of codes holds the coefficients of `1, x, x²` in separate 7-bit groups; `red25` takes `c₀ + 3 c₂`
and `c₁` mod 5 by a multiply-high division (`(205 u) >>> 10 = u / 5` for `u < 1024`), and `red1_sp` is proved by
arithmetic rather than by cases. The order of `SL(2,25)` comes from Mathlib's order of `GL(2,25)` (`card_SL_two`).
`gen_haar25.py` writes the cell (left and right words, D odd).

`gen_haarsl2.py` (SL only) writes the batch modules against `Core/HaarCore.lean`, a copy of the definitions the
kernel evaluates (`batchOK` and what it uses, `kindB`, `aB`, `cB`, `invLet`, `blk`) that imports nothing, so a batch
module starts in about 0.4 s instead of 2.4 s; `HaarSwar2.lean` and `HaarSL2.lean` are `HaarSwar.lean` and
`HaarSL.lean` with those definitions taken from the core file (proofs unchanged), and `Core/Bridge.lean` restates
the core constants (`onesC`, `blk`, whose powers use core's instance) in the `Swar` forms. With 2 batches per module
and raw literals (`--raw --leaf 16384`) a (15,10) batch takes about 4 s under 4 jobs instead of 9.5 s.

Records of generated cells that are not committed are listed in `axioms_big.txt` (the `#print axioms` output of each
record theorem, from the build here). `bigcell.py` streams the largest cells: it writes the batch modules a chunk at a
time, queues them, and deletes each source once its module is built.


# Status: lean-gaps2 (more Lean proofs from GAPS.md, Haar and lift records up to 50,000 vertices)

Branch `claude/lean-gaps2-haar-proofs-9qjlsg`, started from `claude/lean-gaps-proofs-3qf4j2` (the six proofs and
tools of the previous job are there and are not redone). The gap list is `research/lean-haarD/GAPS.md`. Every file
here is new; no existing file is changed.

## Proved (four records, with the axioms of each `Axioms.out.txt`)

| # | Cell | Vertices | Construction | Module folder (`lean/BipartiteDD/Haar/`) | Theorem | Method | Axioms |
|---|---|---:|---|---|---|---|---|
| 1 | (8,5) | 2,048 | route-chart lift (affine fibre maps), 8-regular | `D8D5N2048` | `nb_8_5_n2048` | staged (`gen_d8D5_n2048.py` → `gen_staged_lift.py`) | propext, Classical.choice, Quot.sound |
| 2 | (5,8) | 9,760 | Haar graph of `Z61 ⋊ Z80` (`meta 61 80 8`), S of size 5 | `D5D8N9760` | `nb_5_8_n9760` | Haar, `Eight.lean` lemma, chunked word certificates (`gen_d5D8_n9760.py`) | propext, Classical.choice, Quot.sound |
| 3 | (5,9) | 29,756 | Haar graph of `Z346 ⋊ Z43` (`meta 346 43 29`), S of size 5 | `D5D9N29756` | `nb_5_9_n29756` | Haar, `Diam9.lean` lemma (8-letter covers), 12 chunks per pattern (`gen_d5D9_n29756.py`) | propext, Classical.choice, Quot.sound |
| 4 | (6,8) | 31,680 | Haar graph of `PSL(2,11) × Z24` (order 15840), S of size 6 | `D6D8PSL11Z24` | `nb_6_8_n31680` | Haar, `Eight.lean` lemma, chunked word certificates, PSL(2,11) derived from the D7D8 PSL(2,19) file (`gen_d6D8_n31680.py`) | propext, Classical.choice, Quot.sound |

Edge lists used:
- (8,5): `research/theorems/chartlift/graphs/d8D5_n2048.edges.gz` (copy in the folder). The construction is not a plain
  regular voltage lift as built, which GAPS.md notes; the Lean statement needs only the graph, so the staged pipeline
  applies unchanged.
- (5,8): no edge list on master, only the solution file `research/frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt`.
  The master builder `research/frontier/build_haar2.py` regenerates the graph from it (all-pairs BFS, prints VALID,
  eccentricity 8 from both sides). Its output is copied into the folder as `d5D8_n9760_haar_meta61_80_8.edges.txt`.

## How the link to the graph is checked

- (8,5): `research/lean-haarD/gen_d8D5_n2048.py` reads the edge file, checks it (simple, 8-regular, bipartite, every
  pair within 5 steps by a bitset check), writes `Graph.lean` with the neighbour and colour lists, reads it back and
  asserts that its lists equal the edge file. The staged check then runs as for the other staged records.
- (5,8): `research/lean-haarD/gen_d5D8_n9760.py` reads S from the solution file and checks its header, runs the master
  builder, checks that the Haar graph of S under the numbering `enc(i, j) = 80 i + j` (side A `enc g`, side B
  `4880 + enc g`, `(g, A) ~ (s g, B)`) equals the builder's 24,400 edges, and checks the group law on all elements.
  It then finds one word code per element for each covering pattern of `Eight.lean` (A and B: eight letters, C: seven
  letters), and re-evaluates every code in Python. Lean re-checks each code list by `chkList` (`decide +kernel`) and
  derives the three covering hypotheses (`Cover.lean`).

## Things that did not work first, and what changed

- (5,8), one-module cover check (`(List.range 4880).all okA` with `List.getD` into the code list): killed by the
  kernel's memory at 13.0 GB after 123 s (exit 137). The list is walked once per element, so the cost is quadratic.
- The same check with `rpow` written as `(8 : ZMod 61) ^ j.val` (kernel `Monoid.npow`): still killed at 13.0 GB. The
  power was not the cause, so `rpow` is now `((8 ^ j.val : ℕ) : ZMod 61)` (kernel `Nat.pow`); this change is kept,
  it does not change any statement.
- Final layout: the codes of each pattern are split into four chunks of 1,220 (`CertA0 … CertC3`), each a linear
  check `chkList` by `decide +kernel`, as in `D7D8`. Each chunk module peaks at about 2.6 GB.
- The first `CertA0` attempt failed only on the default `maxRecDepth` of the length lemma (`by rfl` on a 1,220-element
  list); `set_option maxRecDepth 100000` on it fixed it.

## Build measurements

Each module was built with its own `lake build <module>`, one at a time, under a Python wrapper that reads the
largest child's peak RSS (`getrusage`); `/usr/bin/time` is not installed in this sandbox. Machine: 4 cores, 15 GB.

### (8,5) 2,048, module folder `D8D5N2048`

| Module | Wall time | Peak RSS |
|---|---:|---:|
| `Graph` | 28.8 s | 1.00 GB |
| `Level01` | 19.1 s | 1.89 GB |
| `Level02` | 10.4 s | 1.89 GB |
| `Level03` | 8.9 s | 1.89 GB |
| `Level04` | 9.7 s | 1.90 GB |
| `Levels` | 3.8 s | 1.81 GB |
| `Check` (local test, one module) | 46.2 s | 4.67 GB |
| `Stage00` … `Stage04` | 24–30 s each | 3.56–3.58 GB |
| `Record` | 3.5 s | 1.82 GB |
| `Axioms` (`lake env lean`) | 2.1 s | 1.80 GB |

### (5,8) 9,760, module folder `D5D8N9760`

| Module | Wall time | Peak RSS |
|---|---:|---:|
| `Grp` (group axioms, `rpow_add` by `decide +kernel`) | 16.5 s | 2.16 GB |
| `Gens` (S, digits, word functions, `chkList`) | 21.1 s | 2.16 GB |
| `CertA0` … `CertA3` | 19.1–22.0 s each | 2.66 GB each |
| `CertB0` … `CertB3` | 16.5–19.9 s each | 2.66 GB each |
| `CertC0` … `CertC3` | 15.3–18.2 s each | 2.56–2.69 GB each |
| `Cover` | 2.7 s | 1.81 GB |
| `Record9760` | 13.0 s | 1.85 GB |
| `Axioms` (`lake env lean`) | 3.0 s | 1.82 GB |

### (5,9) 29,756, module folder `D5D9N29756`

| Module | Wall time | Peak RSS |
|---|---:|---:|
| `Grp` | 5.3 s | 1.91 GB |
| `Gens` | 3.1 s | 1.80 GB |
| `CertA0` … `CertA11` | 14.7–23.5 s each | 2.69–2.70 GB each |
| `CertB0` … `CertB11` | 13.7–20.6 s each | 2.69–2.70 GB each |
| `Cover` | 3.9 s | 1.83 GB |
| `Record29756` | 4.8 s | 1.87 GB |
| `Axioms` (`lake env lean`) | 2.7 s | 1.84 GB |

### (6,8) 31,680, module folder `D6D8PSL11Z24`

| Module | Wall time | Peak RSS |
|---|---:|---:|
| `PSL11` (group, derived from `D7D8/PSL19.lean`) | 11.0 s | 1.98 GB |
| `Base`, `Gens` | 5.1 s, 5.0 s | 1.82 GB each |
| `CertA0` … `CertA10` | 38–62 s each | 4.41–4.53 GB each |
| `CertB0` … `CertB10` | 38–63 s each | 4.41–4.54 GB each |
| `CertC0` … `CertC10` | 39–50 s each | 4.17–4.18 GB each |
| `Cover` | 4.0 s | 1.87 GB |
| `Record31680` | 4.3 s | 1.89 GB |
| `Axioms` (`lake env lean`) | 3.6 s | 1.87 GB |

Two things that failed first, for (6,8):
- The record with `G` as the product `PSL11.Grp × Multiplicative (ZMod 24)` timed out in elaboration (`whnf`, then
  `isDefEq` at each cover argument, also with 1,000,000 heartbeats). With `sorry` in place of the covers the application
  elaborated in 3.6 s, so the covers' types and the lemma's expected types were not unifying. The fix that worked: `G`
  is a structure `(p : PSL11.Grp, z : ZMod 24)` with its own group instance, as the `Grp` of the (5,8) record. The
  chunks were then rebuilt.

Failed attempt for the record (not kept): the monolithic `CertA` (one `decide +kernel` over 4880 entries) was killed
at 13.02 GB after 123 s.

Toolchain: `leanprover/lean4:v4.34.1` installed with elan in this sandbox, Mathlib from the cache
(`lake exe cache get`, 8,908 files, about one minute).

## Not done in this job, and why

Candidates in GAPS.md with at most 50,000 vertices, Haar or regular voltage lift, and the status of each:

| Cell | Vertices | Construction | Status |
|---|---:|---|---|
| (4,11) | 19,152 | Haar graph of SL(2,8) × Z19, `d4D11_sl_8_19_orb3_e03.txt` | Not proved. The builder validates it (VALID, diameter 11). It needs: GF(8) as a computable `CommRing` (a test compiled in about 8 s on `Fin 8` with XOR addition and a 64-entry multiplication table, scratch only), SL(2,8) with a numbering and bijection proofs in the style of `PSL11`, the product with Z19, covers of length 5 pairs on both sides for the odd-diameter lemma `haar_isBipartiteDegDiam_odd` (GraphD.lean), and a conversion from the chunk checks to `IsLeftWord`/`IsRightWord`. Estimated at about three hours, so not started to completion. |
| (12,5) | 9,840 | regular Z6 lift of the GQ(9) doubled-matching base; `research/d10D7/graphs/d12D5_n9840_gqdm_q9.edges.gz` | Not done. The staged method stores the ball masks of radius 1 … 4 as n-bit hex literals (n² bits): about 97 MB of Lean data for this record, against 46 MB for the (11,5) record already on the branch. Too large for the repository without a change of method. |
| (13,5) | 11,700 | regular Z10 lift of the GQ(8) doubled-matching base; `research/frontier/beyond/graphs/d13D5_n11700_W8_2dm_Z10.edges.gz` | Not done, same reason (about 130 MB of masks). |
| (14,5) | 17,568 | regular lift, `research/d10D7/graphs/d14D5_n17568_gqdm_q11.edges.gz` | Not done: masks about 300 MB. |
| (15,5) | 20,736 | route-chart lift, `research/theorems/chartlift/graphs/d15D5_n20736.edges.gz` | Not done: masks of the same order (n²). |
| (16,5) | 33,792 | route-chart / doubled-matching, `research/theorems/graphs/d16D5_n33792_k33m_z22.edges.gz` | Not done: n² masks of several GB of hex. |
| (18,5) | 47,600 | doubled matching over Z10, `research/frontier/beyond/graphs/d18D5_n47600_W13_2dm_Z10.edges.gz` | Not done: n² masks. |
| (4,12) | 50,160 | orbit search (`d4D12_sl_11_19_orb3_d09.txt`) | Not done: 50,160 is above the job's limit of 50,000 vertices. It is listed as an example in the job, so this is flagged. |

The (5,8), (5,9) and (6,8) Haar records above were the Haar candidates that had a usable solution file and a builder.
(8,5) is a route-chart lift, which the job named, so it is included even though it is not a plain voltage lift.

For the lift records, the cost is the staged method's ball-mask data, which grows as n². Either the data would have to
move out of git (for example an artifact store, as GAPS.md suggests) or the method would have to change. Neither was
done here.

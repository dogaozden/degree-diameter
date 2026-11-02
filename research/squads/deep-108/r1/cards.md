# deep-108 squad round 1 (cards written by the Opus coordinator, 2026-11-01 ~23:15 UTC)

Goal of the cell: a bipartite graph, max degree 10, diameter 8, more than 1,176,480 vertices.
Family under study: bi-coset graphs X(G; L, R; D): A-vertices = left cosets L x, B-vertices = left cosets R y,
L x ~ R y iff x y^-1 in D, D = L z R one double coset. With |L| = |R| = 10 and L ∩ z R z^-1 = 1 every vertex has
degree 10 and there are |G|/10 vertices per side. Cost C = uBA + uAA + uBB (uncovered vertices, 0 = diameter 8).

Why special orbits matter (read this): the A-root BFS runs on L-orbits of B-cosets. An orbit of size s (stabiliser of
order 10/s) is covered with probability about 1 - exp(-lambda*s/10), lambda = 5,380,840/N (about 9). Regular orbits
(s = 10) are cheap to cover; size-2 orbits (stabiliser C5) are missed with probability about 0.17-0.22 each, size-5
orbits (stabiliser C2) about 0.011-0.02 each. `info` prints the census "c1:.. c2:.. c5:.. c10:.." of B-orbit sizes.
Special burden E_s = sum over non-regular orbits of exp(-lambda*s/10). Family K (PSL(2,229), L = R = D5) has
E_s = 3.5 and exhaustive minimum C = 4 (two size-2 orbits missed). An orbit stabilised by l in L exists iff l is
G-conjugate into R, so choosing L, R with no G-conjugate non-identity elements gives E_s = 0.

Tools (built by the coordinator, validated; do not edit them, copy if you must change something):
- research/squads/deep-108/cq/cq2  : G = PSL/PGL(2,q) x Z_m. Every element is 5 ints "a b c d res" (matrix, residue).
  usage: cq2 q psl m NL gens(5 each) NR gens(5 each; NR=0 means R = L) MODE ...
- research/squads/deep-108/cq/cq3  : G = A x PSL(2,p), A a subgroup of PSL(2,p). Elements are 8 ints "A-matrix Q-matrix".
  usage: cq3 p NA A-gens(4 each) NL gens(8 each) NR gens(8 each) MODE ...
- MODES: info (census) | member 1 z (costs of D = L z R, z as one element) | unc 1 z (list uncovered orbits) |
  scanLR OUT THR [start step] (every regular double coset L z R, members with index = start mod step; A-root cost,
  plus B-root if uBA+uAA <= THR; resumable: skips ids already in OUT; one line "M id 1 uBA uAA uBB z...") |
  bench n.
- research/squads/deep-108/a5/gens.py p : prints A5 generators inside PSL(2,p), r (order 5), r2 = r^2, t (involution
  inverting r), s (involution commuting with r). Matrices are "a b c d" mod p.
- Speed: one A-root BFS about 17-20 ms. A full family is about 60,000 members, about 20 core-minutes.

Shared rules (every card):
- Work only in research/squads/deep-108/r1/<card>/. No git commands. Do not edit files outside your folder.
- Machine: 4 cores and 15 GB shared with the coordinator and 2 other workers. Use one core: prefix heavy commands with
  `nice -n 10`. Memory below 1.5 GB per process (cq2/cq3 use about 0.2-0.4 GB).
- KEEP EVERY COMMAND UNDER 110 SECONDS. Never start a background process (no nohup, no &): a background job makes you
  end your turn and idle. Run long work as a chain of foreground commands of at most 100 s each
  (`timeout 100 nice -n 10 ...`; scanLR is resumable, so just rerun the same command until it says "done", or use
  start/step chunks).
- Do not end your turn while work is unfinished. When you are done, append ONE line of JSON to
  research/squads/deep-108/r1/scoreboard.jsonl:
  {"card": "c1", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <lowest C found, connected
  members only>, "valid": false, "next": "<one line>"}
  and reply in at most 8 lines (best member z and its C, census, medians, what is worth more CPU).
- A member is connected only if uBA + uAA is small (a disconnected graph shows uBA in the hundreds of thousands).
- If you find C = 0: write the exact command and z to your folder as CLAIM.txt, stop, and say so in your reply. The
  coordinator verifies everything independently; your result is a claim, not a proof.
- Time box: about 90 minutes of work.

## c1-a5: A5 x PSL(2,59), zero-special pairs (|G| = 6,159,600, N = 615,960)
The coordinator found one pair with E_s = 0: with r, r2, t, s from `python3 ../../a5/gens.py 59` and I = "1 0 0 1",
  A = "2 13 7 1 46 16 26 52 44" (A5 inside PSL(2,59)), L = "2 $r $r $t $t" (diagonal D5),
  R = "2 $r $r2 $I $s" (C10: (r, r^2) and (1, s)); census c10:61596 (no special orbits).
  A sample of 292 members: min 140, p10 230, median 580 (K: median about 340).
Tasks: (1) Run the exhaustive scanLR of this pair (out file pair0.tsv, THR 300) in resumable chunks to the end;
report the minimum C over connected members and the 10 best. (2) Enumerate other inequivalent zero- or low-special
pairs in this group: other twists (for example L = <(r, r), (t, t)>, R = <(r, r2), (t, t)> (twisted D5),
R = <(r2, r), (I, s)>, L = <(r, r2), (t, t)>, swapping which factor carries the C2), compute each census with
`info`, and sample 300 members each (scanLR with a step of about 200). Rank pairs by E_s and by the sample median.
(3) If a pair beats pair0 clearly on the sample, scan it exhaustively too.

## c2-z2: PSL(2,181) x Z2 and twisted subgroups (cq2, |G| = 5,929,560, N = 592,956)
Elements are "a b c d res" with res mod 2. In PSL(2,181): x = "1 0 0 42 0" has order 5 (diagonal), y = "0 1 180 0 0"
is an involution inverting it, and c10 = "1 0 0 139 0" has order 10 (139 = -42; its 5th power is the involution of
the diagonal torus). Check orders with `info` (it prints the order of every element of L).
Order-10 subgroups up to conjugacy: D5x0 = <(x,0), (y,0)>, C10x0, D5' = <(x,0), (y,1)> (twisted), C10' = <(c10,1)>
twisted. Note: a subgroup containing the central element (I,1) gives a degenerate graph; skip it.
Tasks: (1) For every pair (L, R) of these four classes (including L = R), run `info` (census, E_s) and a 300-member
sample (scanLR with step about 200); drop disconnected families. (2) Rank by E_s and sample median; scan the best
pair exhaustively in resumable chunks; report min C and the 10 best.

## c3-wild: a family none of the others tries
Tried so far (do not repeat): Haar graphs with alpha-orbits (k = 3) on PSL(2,23) x Z97 and PSL(2,7) x SL(2,8) x Z7;
coset families over PSL(2,229) (D5), PGL(2,181) (D5 sq/nsq, C10, bi-coset pairs), PSL(2,181) C5 two double cosets,
h = 6 and h = 12 families, non-regular double cosets (families with |L ∩ zLz^-1| = 2 are tiny: about 135 members);
A5 x PSL(2,59) and PSL(2,181) x Z2 (cards c1, c2); voltage lifts of the split Cayley hexagon H(q) + matchings.
Task: find one more construction of degree-10 bipartite graphs with more than 1,176,480 vertices and plausible
diameter 8 that the tools cq2/cq3 (or a small extension you write in your folder) can evaluate, for example: other
group orders in [5,882,410, 6,200,000] with order-10 subgroups (products, extensions you can implement), bi-coset
graphs with |L| != |R| that still have max degree 10, unions of two double cosets of order-5 subgroups with special
orbits removed by the bi-coset trick (L = C5, R = a non-conjugate C5 in a product group), or anything else. Explain
in your notes why the special burden E_s and lambda make it competitive with K (E_s 3.5, mu/h 7.7), then sample it.

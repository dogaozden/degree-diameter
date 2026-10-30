# Squad d75-r1: shared rules (read first)

Goal: a bipartite graph with maximum degree 7 and diameter exactly 5 on MORE than 1,200 vertices (cell (7,5) of the
bipartite degree-diameter table). Our record: 1,200 = Haar graph H(G,S) of G = SL(2,5) x C5 = SmallGroup(600,54),
|S| = 7, S invariant under an involutory automorphism of G (found again by research/d75-raise/src/haar75 in 0.1 s).

Haar graph H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B). Diameter <= 5 iff X X = G and Y Y = G (and Y Y S = G)
with X = S^-1 S, Y = S S^-1. That is 1,555 even walks for |G| targets, so |G| = 601..660 is hard: structure is needed.

Machine: 4 cores and 15 GB shared with the director's sweep and 7 other cards. THREADS=1; run anything heavy as
`timeout 900 nice -n 10 <cmd>`; at most ~1.5 GB of memory; no git commands that change anything (no commit, no
checkout, no stash); write only inside your card folder research/squads/d75-r1/<card>/ ; use TMPDIR=<your folder>/tmp.
Time box: about 20 minutes of wall-clock, then report.

Tools (repo root /home/user/degree-diameter):
- research/d75-raise/src/export.g: GAP export of SmallGroup(N,ID) (or any group G bound before reading it) to a
  multiplication table + prime-order automorphism classes; usage in research/d75-raise/src/run1.sh.
- research/d75-raise/src/haar75.c (built: research/d75-raise/src/haar75): `haar75 FILE.ht exh` = every Haar graph whose
  S is invariant under an automorphism of prime order; `SECS=60 SEED=1 haar75 FILE.ht sa` = plain annealing.
  EDGES=out.edges writes the first solution. Read its header comment for the cost definition.
- Scorer (all-pairs BFS, no symmetry assumed): `research/d75-raise/src/apsp EDGES 7 5` -> last line
  "RESULT VALID d=7 D=5 n=N" or INVALID. Edge list format: first line = number of vertices, then "u v" per edge.
- Older tools on other branches (read with `git show BRANCH:PATH > yourfolder/file`):
  origin/claude/beyond-haar-d5-records-ik8bce: research/beyond-haar-d5b/coset/{dcenum.c, dc2_lib.g, sweep.sh,
  dc2_edges.py} (bi-coset graphs B(G;H,K)), research/beyond-haar-d5b/src/{vl.c, kopt.c, gap_tables.g} (voltage lift
  annealer + exact k-opt), research/beyond-haar-d5/README.md and research/beyond-haar-d5b/README.md (what was tried);
  origin/claude/squad-6-5-rounds-ts5nxk: research/s65/tabu/tabu.c, research/s65/tools/{mcos.c, kdesc.c, bicay.c}.
- GAP 4.12 with the SmallGroups library is installed (`gap -q file.g`).

Already covered (do not redo): the director runs haar75 exh on every non-abelian group of order 601-660 except 600 and
640. Near misses so far: SmallGroup(605,4) = (C11 x C11):C5 cost 2 (two elements missed), SmallGroup(609,1) cost 8.
Earlier jobs: bi-coset graphs |H| = 2 annealed for orders 1202-1276 with <= 60 groups (best 12); |H| = 3 for
SmallGroups of order 1731-1929 with <= 60 groups (best 2 at 1210, Haar in disguise); random 2+2 lifts over few-involution
groups of order 304-336 (best 20+).

Scoreboard: append ONE line of JSON to research/squads/d75-r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <vertices if valid, else best
cost>, "N": <vertices of the best graph>, "valid": true|false, "next": "<one line>"}
If you find a VALID graph above 1,200: keep its edge list in your folder and put "valid": true. Reply to the director in
at most 5 lines.

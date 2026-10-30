# Squad d75-r2: shared rules (read first)

Goal: a bipartite graph with maximum degree 7 and diameter exactly 5 on MORE than 1,312 vertices (cell (7,5)).
Our record (this job, an hour ago): 1,312 = Haar graph H(G,S), G = C41 : C16 = SmallGroup(656,28); before it 1,240
(C31 : C20 = SmallGroup(620,1)). Also 1,210 (SmallGroup(605,6)), 1,204 (SmallGroup(602,2)), and the old 1,200
(SL(2,5) x C5 = SmallGroup(600,54)).

THE IDEA THAT WORKED (read research/d75-raise/README.md, section "How: self-dual connection sets"):
Haar graph H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B). Diameter <= 5 iff X X = G and Y Y = G (and Y Y S = G),
X = S^-1 S, Y = S S^-1. If psi(S) = S for psi(x) = beta(x)^-1 with beta in Aut(G), the map (g,A) -> (beta(g),B),
(g,B) -> (beta(g),A) is a colour-swapping automorphism, so X X = G already implies Y Y = G: half the test.
`research/d75-raise/src/haar75 FILE.ht anti` enumerates every S that is a union of psi-orbits (beta = identity or
an involutory automorphism class rep; also beta of order 4), identity in S. All hits are type (3,2): S = {e, f1, f2}
(psi-fixed: beta(f) = f^-1) + two psi-pairs {g, beta(g)^-1}. Solutions (element numbers of export.g's table) are in
research/d75-raise/logs/exh/*_anti.out (SOL lines) and research/d75-raise/records/sg*_anti_solutions.txt.
Both big hits are G(p,d) = C_p : C_2d with y acting with order d and y^d the central (unique) involution.
Calibration: on SL(2,5) x C5 the anti mode finds 26 solutions vs 4 for plain automorphism-invariant sets.

The director is running `haar75 anti` on every non-abelian group of order 621-720 (groups with <= 1 involution first,
then 3, then the rest) and on G(p,d) for orders 666-776. Do NOT re-run haar75 anti on plain SmallGroups lists; each
card below is a DIFFERENT family or method.

Machine: 4 cores shared with the director's sweep (which has priority) and 7 other cards. THREADS=1; run anything
heavy as `timeout 900 nice -n 15 <cmd>`; at most ~1.5 GB of memory; no git commands that change anything; write only
inside research/squads/d75-r2/<card>/ ; use TMPDIR=<your folder>/tmp. Time box: about 25 minutes of wall-clock.

Tools (repo root /home/user/degree-diameter): research/d75-raise/src/{export.g (GAP export: table, inverses, prime and
order-4 automorphism classes with centralizers; INVS:=true adds involution classes), haar75.c, bic75.c (bi-coset
graphs |H| = |K| = 2, exhaustive), lift22.c (4-vertex-base lifts), allaut.g (all automorphisms as permutations),
sdcheck.c, apsp (scorer)}. Read the header comments. GAP 4.12 with SmallGroups is installed.
Scorer: `research/d75-raise/src/apsp EDGES 7 5` -> last line "RESULT VALID d=7 D=5 n=N" (all-pairs BFS). Edge list:
first line = number of vertices, then "u v" per edge.

Scoreboard: append ONE line of JSON to research/squads/d75-r2/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <vertices if valid, else best
cost>, "N": <vertices of the best graph>, "valid": true|false, "next": "<one line>"}
A VALID graph above 1,312: keep the edge list in your folder, "valid": true. Reply in at most 5 lines.

# Squad sd5b-r1: shared rules (read first)

Goal: a bipartite graph with maximum degree 9 and diameter 5 on MORE than 3,036 vertices (cell (9,5); our record 3,036
is the Haar graph of C69 : C22, order 1518). Here: a self-dual Haar graph H(G,S), |S| = 9, of a group G of order
|G| >= 1519 (2|G| vertices).

Background (research/selfdual-d5/README.md): Haar graph H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B). If S is a
union of orbits of psi(x) = beta(x)^-1 for an involutory automorphism beta of G (or beta = identity), the graph is a
bipartite Cayley graph and diameter <= 5 iff X X = G, X = S^-1 S. The tool below searches exactly these sets by tabu:
types (f, m) = e + (f-1) psi-fixed elements + m psi-pairs, f + 2m = 9; types (1,4), (3,3), (5,2) are the useful ones.
Energy = |G \ X X| (0 = valid). Previous hits at orders 1395-1518 came from groups with a large normal cyclic subgroup
and a small top (C_p : C_k, C_m : C_k), and also Heis(3) x (C11 : C5) (1485), C31 : (C3 x Q16) (1488),
(C5)^3 : (C3 : C4) (1500), C7 : (C3 x ((C3 x C3) : C8)) (1512). Near misses above 1518: SmallGroup(1539,31) and
(1539,45) (energy 2 after 300 s runs). The director is already sweeping: all metacyclic C_m : C_k of order 1519-1650,
affine F_p^d : C_k (cyclic top), and the SmallGroups of order 1520-1560 that have a normal Sylow p-subgroup of prime
order p acting with order >= 3. Do NOT repeat those; each card is a different family or method.

Tools (repo root /home/user/degree-diameter; do not recompile in src/, copy to your folder if you change code):
- Export a group to the tool's format (multiplication table, inverses, involution classes of Aut(G)), any GAP group G:
  `gap -q -c 'G:=<GAP expression>;; OUT:="<your folder>/x.ht";; NOEXT:=1;;' research/selfdual-d5/src/export_sd.g`
  (SmallGroup(N,ID) also works: `N:=1539;; ID:=31;;` instead of G). About 10 s at order 1500.
  Example: G:=DirectProduct(SmallGroup(27,3), SmallGroup(55,1)) is the 2,970 group (order 1485).
- Search: `K=9 SECS=3 NB=48 STALL=1000 TYPES=1,3,5 NOID=1 SEED=1 EDGES=<folder>/sol.edges research/selfdual-d5/src/sdtabu2 x.ht all`
  prints one line "TABU rec R alpha 2 f F m M best B ..." per (record, type) (B = smallest energy reached) and
  "SOL ..." for each solution; the first solution's edge list goes to EDGES. Long run on one record/type:
  `K=9 SECS=300 NB=96 STALL=2000 ENDG=3 SEED=7 EDGES=... research/selfdual-d5/src/sdtabu2 x.ht R F M`.
  Source: research/selfdual-d5/src/sdtabu2.c. Calibration: on the 1485 example, record 5 type (3,3) reaches 2 in 2 s
  (and has solutions); on C197 : C7 (`research/selfdual-d5/src/meta_export.py 197 7 104 x.ht`, record 1 type (3,3))
  it finds about 25 solutions per 100 s.
- Formula metacyclic export (no GAP): `python3 research/selfdual-d5/src/meta_export.py m k r x.ht`.
Scorer: smallest energy B over your runs (lower is better) at an order |G| >= 1519; for B = 0,
`research/selfdual-d5/src/apsp <folder>/sol.edges 9 5` must print "RESULT VALID d=9 D=5 n=<2|G|>".

Machine: 4 cores shared with the director's sweeps (priority) and 7 other cards. THREADS=1; run anything heavy as
`timeout 900 nice -n 15 <cmd>`; at most ~1.5 GB memory; no git commands that change anything; write only inside
research/squads/sd5b-r1/<card>/ ; use TMPDIR=<your folder>/tmp. Time box: about 25 minutes wall-clock.

Scoreboard: append ONE line of JSON to research/squads/sd5b-r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <best energy B, 0 if valid>,
"N": <|G| of the best attempt>, "group": "<GAP expression or SmallGroup id>", "rec_type": "<R f m>", "valid": true|false,
"next": "<one line>"}
Keep the .out files of your sdtabu2 runs in your folder. Reply to the director in at most 5 lines.

# Squad conics-r1 (2026-10-29): independent checks for research/synthetic/CONICS.md

Goal: independently verify (or refute) claims of the Opus session on conics in the hat constructions, and run two
small searches. Write your own code from the definitions below; do NOT import or copy code from
research/synthetic/conics/ (that is the code being checked). You may read research/plus2/coords/coords.py for GF(q)
arithmetic, and use any python in /tmp/claude-0/-home-user-degree-diameter/db23ed3e-5ef1-51fa-9a71-0fdc3180aa1f/scratchpad/venv/bin/python
(it has python-sat and numpy).

Machine rules: about 4 cores are shared; THREADS=1; wrap anything heavy as `timeout 900 nice -n 10 <cmd>`; at most
1.5 GB of memory; no git commits; write only inside your card folder research/squads/conics-r1/<card>/; time box
about 20 minutes.

Output: append ONE line of JSON to research/squads/conics-r1/scoreboard.jsonl:
{"card": "c1", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "valid": true|false,
 "next": "<one line>"}
and reply in at most 5 lines (what you checked, the result, anything that failed).

## Definitions (shared by all cards)

PG(2,q): points are nonzero triples (x,y,z) over GF(q) up to scalars, lines are triples [a,b,c] up to scalars,
(x,y,z) lies on [a,b,c] iff ax+by+cz = 0.

Conic C: x z = y^2 (q odd). Its polarity: point (x,y,z) -> line [z, -2y, x]; line [a,b,c] -> point (c, -b/2, a).
A point p is on C iff p lies on its own polar line. Conjugate points: p, r with r on the polar of p.

Frame: A = (0,1,0), ell = polar of A = the line [0,1,0] (y = 0). ell meets C in Z = (1,0,0) and Z' = (0,0,1).
On ell the conjugation is (1,0,u) <-> (1,0,-u), fixing Z and Z'. For a point X of ell write lam(X) = the line AX.

The hat structure S (rules from research/synthetic/SYNTHETIC.md, Definition 1.1, branch
claude/synthetic-incidence-geometry-s4m08f). Labels: three hats S = {0,1,a}, T = {0,1}, links pi = (0 1), no rotation;
four hats S = {0,1,a,c}, T = {0,c,1}, pi = rho = sigma with sigma(0)=c, sigma(c)=1, sigma(1)=0.
Marked points X_s on ell; lam_s = A X_s; ell* = points of ell other than X_t (t in T); Lam* = lines through A other
than lam_t (t in T). New points Q, H_s; new lines M, K_s. Incidences, exactly:
 (R1) all incidences of PG(2,q) except the flags (X_s, lam_s) for s in S; plus the flags (X_t, lam_{rho(t)}) for t in T
      (for three hats rho = identity, so only (X_a, lam_a) is really deleted);
 (R2) H_s lies on every line through X_s other than ell;
 (R3) K_s contains every point of lam_s other than A;
 (R4) M contains the points of ell* and every H_s;
 (R5) Q lies on the lines of Lam* and on every K_s;
 (R6) A on K_a; H_a on ell; H_t on K_{pi(t)} for t in T.

Conic-adapted frame (the claim): three hats X_a = Z, X_0 = (1,0,u), X_1 = (1,0,-u) (u != 0);
four hats additionally X_c = Z'. Let tau swap the labels 0 and 1 and fix a, c. Define theta: old point p -> its polar
line, old line -> its pole, H_s -> K_{tau(s)}, K_s -> H_{tau(s)}, Q -> M, M -> Q.

CLAIM 1 (Prop. 1.2): theta is a polarity of S: theta(theta(x)) = x, and (p, L) is a flag of S iff
(theta(L), theta(p)) is a flag of S. S has maximum degree q+2 and its incidence graph has diameter 3.

CLAIM 2 (fold): the graph G on the points of S with p ~ p' iff p != p' and p is on theta(p') is a simple graph
(symmetric), of maximum degree q+2 and diameter 2, with q^2+q+5 (three hats) or q^2+q+6 (four hats) vertices.

CLAIM 3 (Prop. 1.4, explicit regular completion): in S the elements of degree q+1 ("deficient") are points and lines
of PG(2,q). Match each deficient point p to the line mu(p) = polar of p if p is not on C, and mu(p) = polar of p*
if p is on C, where p* is the second point of C on the line A p. Then mu is a bijection from the deficient points onto
the deficient lines, p is never on mu(p), and S plus the flags (p, mu(p)) is (q+2)-regular with diameter 3, and is
still self-polar under theta.

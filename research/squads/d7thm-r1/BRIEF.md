# Squad round d7thm-r1: independent checks for research/synthetic/D7_THEOREMS.md

Job "thm-conics" (29 October 2026). Opus writes theorems about the diameter-7 freed sets; each card re-checks one
ingredient by an independent program. Write your own code (do not read research/synthetic/conics2/typed_build.py or the
d7thm/ scripts). Work only in your card folder research/squads/d7thm-r1/<card>/. No git commits. THREADS=1;
`timeout 900 nice -n 10 <cmd>` for anything heavy; at most 1.5 GB memory. Append ONE JSON line to
research/squads/d7thm-r1/scoreboard.jsonl when done:
{"card": "cN", "idea": "...", "code": "<path>", "command": "<exact>", "score": <number of checks passed>, "valid": true|false, "next": "..."}
and reply in at most 8 lines (what passed, what failed, with numbers).

## Geometry (all cards)

q a prime power, F = GF(q). For q = 4, 8, 9 use elements 0..q-1 encoding a0 + a1 p + ... (p the characteristic) modulo
x^2+x+1 (q=4), x^3+x+1 (q=8), x^2+1 (q=9) (the encoding of research/d10D7/hexgen2.c).

Quadric Q(X) = X0X4 + X1X5 + X2X6 - X3^2 on F^7 (q odd); Q(X) = X0X4 + X1X5 + X2X6 + X3^2 (q even). Points of H(q):
the projective points with Q = 0, N = (q^6-1)/(q-1) of them. Lines of H(q): the projective lines <x,y> contained in the
quadric whose Pluecker coordinates p_ij = x_i y_j - x_j y_i satisfy
  p12 = p34, p54 = p32, p20 = p35, p65 = p30, p01 = p36, p46 = p31.
Equivalent way to get the lines through a point x: the points y != x with Q(y) = 0, B(x,y) = 0 (B the polar form) and the
six equations above form, with x, a plane's worth of q(q+1) points on q+1 lines through x. Sanity: N lines, q+1 points
per line, q+1 lines per point, incidence graph of diameter 6 and girth 12. You may instead compile
research/d10D7/hexgen2.c (`cc -O2 -o hexgen2 hexgen2.c && ./hexgen2 q` writes hex/hex_q{q}.bin: int32 q, N, L, then
L*(q+1) int32 point ids, then N*7 uint8 coordinates in the encoding above); cards c1 and c3 must build H(q) themselves for
the prime q they check, and may use hexgen2 for the others.

Distances are in the incidence graph I (points and lines as vertices). Opposite = distance 6. A point set F is a
*segment set* if for every p in F the points of F \ {p} collinear with p all lie on one line through p. A line set G is a
*dual segment set* if for every l in G the lines of G \ {l} meeting l all pass through one point of l.

### The sets (q odd)
c in F with -c a non-square. Pi: X0 + c X4 = 0; S = the lines of H(q) contained in Pi (the Hermitian spread, q^3+1 lines,
pairwise opposite); P_S = the points on lines of S ((q+1)(q^3+1) of them, exactly the points of H(q) in Pi).
v = the line through e1 = (0,1,0,0,0,0,0) and e6 = (0,0,0,0,0,0,1) (it lies in Pi, so v is in S).
L_v = the q(q+1) lines != v meeting v. Points at distance <= 3 from v: exactly the points with X2 = X5 = 0.
Free points: points not in Pi and at distance 5 from v (q^3(q^2-1) of them).
For z = (alpha, beta) in F^2: Pi_z: X0 + c X4 + alpha X2 + beta X5 = 0, S_z = lines of H(q) inside Pi_z.
nu(X) = (X2 X3 - X4 X5) / (c X2^2 + X5^2) for X a point of Pi not on v (well defined projectively).
G(a,b) = (c0 a + c1 b)(a^2 + c b^2) - b^3 with c0, c1 chosen so that G(a,b) != 0 for all (a,b) != (0,0).
F(z) = G(alpha,beta) / (alpha^2 + c beta^2).
W = { l in S_z, l != v : z != 0, nu(l meet Pi) = F(z) }   (l meets Pi in exactly one point).
### The sets (q even, q >= 4)
delta in F with absolute trace 1. Q = X0X4 + X1X5 + X2X6 + X3^2. Pi_z: X3 = X0 + delta X4 + alpha X2 + beta X5, Pi = Pi_0,
S, P_S, v, L_v, free points as above. nu(X) = (X2X3 + X2X4 + X4X5) / (delta X2^2 + X2X5 + X5^2).
G(a,b) = (c0 a + c1 b)(a^2 + a b + delta b^2) + b^3 zero-free on F^2 \ 0; F(z) = G(alpha,beta)/(alpha^2 + alpha beta + delta beta^2).
W as above.
### Derived sets
S_0 = the lines of S other than v that meet no line of W. R_H = P_S. R_L = L_v + W + S_0.
Claims to test: |W| = q^2(q^2-1) and every free point is on exactly one line of W; nu is constant on every line of S
other than v; every line of S other than v meets either q+1 lines of W (one at each of its points) or none; exactly q^2
lines of S other than v meet none, and they are exactly those with nu = 0; R_L is a dual segment set with
q^4 + q^2 + q lines; every point of H(q) is on a line of R_L, and no line outside R_L can be added (maximal); R_H is a
segment set with (q+1)(q^3+1) points.
Elliptic section: a 3-space Sigma of PG(6,q) whose intersection with the quadric is an elliptic quadric (q^2+1 points,
containing no line); its points are pairwise opposite in H(q).

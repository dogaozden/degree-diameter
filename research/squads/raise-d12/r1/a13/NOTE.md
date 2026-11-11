# a13 idea (wildcard for (4,12), target N >= 35,089 i.e. 2N > 70,176)

Orbit-closed Haar search on a NILPOTENT group with a fixed-point-free automorphism alpha of order 3.
Thompson: fpf automorphism of prime order forces nilpotency; each Sylow must have order = 1 mod 3 with fpf
action. Candidates in the target range with a nonabelian factor:
  G1 = Heis(F_13) x Z_2^4 (= Heis(13) x F_4^2), N = 2197 * 16 = 35,152
  G2 = Heis(F_7) x Z_103,                       N = 343 * 103 = 35,329
  G3 = Heis(F_13) x Z_4^2,                      N = 35,152
Heis(F_p) = {(a,b,c)}, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a b'), alpha(a,b,c) = (w a, w b, w^2 c), w^3 = 1 mod p:
fpf, order 3. S = {e, x, alpha x, alpha^2 x}: only N-1 candidates, so the scan is exhaustive.
Heuristic: holes come in alpha-clumps of 3, so P(no hole) ~ exp(-mu/3) with mu ~ 18 at N = 35,100 (SIZE_LAW),
i.e. about 0.25 % per candidate, ~80 hits expected if the random-graph law holds.
Risk: class-2 groups have a small commutator subgroup (Z_13 or Z_7) and small abelianization, so word
coincidences may be heavier than in the Frobenius records. The scan measures this.
Scorer: own BFS (two sources (e,A),(e,B), since the graph is vertex-transitive on each side), then apsp on the edge list.

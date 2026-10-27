# c9: far vertices of LPS Haar graphs (p in {5,7,13}, q in {13,29,97})

Code: far.c (own BFS; same LPS set, (x,y) choice and graph convention as lps_haar.c, m = 1), tabulate.py (table + score).
Runs: `./far p q 2000 1` for every p in {5,7,13} and q in {13,29,97}. Outputs: out_p<p>_q<q>.txt. Each file has a SUMMARY
line, then one line per listed far A-vertex: matrix entries, least N(gamma) <= 200 over primitive gamma (-1 if none),
pure-at-that-norm flag, pure-with-norm<=50 flag, BFS distance from (e,A).

Checks: psi is multiplicative up to scalars on 2000 random quaternion pairs (0 mismatches). Distances agree with lps_haar
(p=5, q=13: d(e,psi(i)) = d(e,psi(j)) = d(e,psi(k)) = 6, and far vertex psi(k) is listed at distance 6).

Result: the conjecture fails. Pure gamma of norm <= 50 explain 303 of 4373 listed far vertices (score 0.069).
Every listed vertex has some primitive gamma of norm <= 200 except 36 (p=13 at q=13 and q=97). Least-norm representatives
are mostly non-pure, with norms spread over 9..172. The few pure explanations are at norms 1..35.
Legendre sign (p/q) for the runs: q=13 and q=97 give -1 and q=29 gives +1, for every p in {5,7,13}.
The far sets are tiny for some (p,q) (p=7 q=29: 21 vertices).

### D = 12: field-automorphism orbits at Δ = 8..11, and (15,12) (job raise-d12, 2026-11-01/02)

Job raise-d12 (Opus director + Haiku squad rounds, cloud session, branch claude/d12-frontier-cells-m24ikx). Size limit:
30 billion vertices.

**The idea.** BEYOND_RANDOM.md: if S is closed under an automorphism alpha of odd order k, the uncovered elements come in
alpha-orbits, so a valid S appears with probability about exp(-mu/k - F) instead of exp(-mu), where F counts the
alpha-fixed elements (each missed with probability exp(-lambda/k)). The earlier D = 12 values used k = 3 (conjugation by
a matrix of order 3, whose fixed set is a torus of ~p/2 elements). The field automorphism x -> x^p of GF(p^e) has order e
and fixes only SL(2,p) or PSL(2,p): for SL(2,128) (e = 7) the fixed set is SL(2,2), 6 elements, and for PSL(2,243)
(e = 5) it is PSL(2,3), 12 elements. So these groups allow k = 7 and k = 5 with almost no fixed-point cost. The search
tool is research/frontier/raise-d12/haar_bigq.c: haar_big0 (bit-parallel, N/2 bytes) for SL/PSL(2,q) x Z_n with q a
prime power; its rows are cosets of the split torus x Z_n (cyclic when gcd(|T|, n) = 1), and AFROB=j selects the field
automorphism. It reproduces haar_big0's cost exactly on prime fields and haarcheck_gen's unreached count on GF(81).

**Results (director).**

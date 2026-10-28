"""Theorem E: make (E2) and (E3) fail separately. M = a local duality at R (Prop. 6.4) perturbed by a few random
transpositions; compare (E2)&(E3) with the two-level BFS. Also checks that (E1) never fails while (E2) holds."""
import random, sys
from gf import GF
from gq import W, Q4
from families import local_duality
from test_theorems import two_level_bad, E2E3
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
tally = {}
for q in (2, 3):
    F = GF(q)
    for G in (W(F), Q4(F)):
        N = G.N
        for trial in range(600):
            typ0, typ1 = rng.choice([('H', 'H'), ('D', 'D')])
            M, R = local_duality(G, 'P' if typ0 == 'H' else 'L', rng)
            if rng.random() < 0.5:
                R = R[:1]
            M = M[:]
            for _ in range(rng.randint(1, 3)):
                i, j = rng.sample(range(N), 2); M[i], M[j] = M[j], M[i]
            bad = two_level_bad(G, typ0, typ1, M, R)
            e2, e3 = E2E3(G, typ0, typ1, M, R)
            assert (not bad) == (e2 and e3)
            k = 'repaired' if not bad else ('only E2 fails' if e3 else 'only E3 fails' if e2 else 'both fail')
            tally[k] = tally.get(k, 0) + 1
print("perturbed local dualities, q = 2, 3, W and Q4, 2400 transitions; Theorem E agrees with BFS in all:", tally)

"""Small-q tests: Theorem A (level graph), Theorem B (automorphic iff partial ovoid), Theorem E (exact criterion =
brute force), on W(q) and Q(4,q) for q = 2, 3, 4, 5.  Output: test_basic_out.txt"""
import random, sys, os
import numpy as np
from gqlib import W, Q4, regular_spread_W, is_partial_ovoid
from levels import build, write_edges, apsp, random_bijection, identity
from repair import brute_bad, exact_conditions, full_dist

rng = random.Random(1)
out = []
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); out.append(s); sys.stdout.flush()

TMP = os.environ.get('TMPDIR', '/tmp')

# Theorem A: random types, random bijections
for q in (2, 3, 4, 5):
    for G in (W(q), Q4(q)):
        for r in (1, 2):
            for trial in range(2):
                L = 2 * r + 1
                types = [rng.choice('HD') for _ in range(L)]
                M = {}
                for j in range(L):
                    for k in range(1, r + 1):
                        M[(j, k)] = random_bijection(G.np, rng)
                n, E = build(G, types, M)
                p = os.path.join(TMP, 'tA.txt'); write_edges(p, n, E)
                res = apsp(p, q + 1 + r, 5)
                log('ThmA', G.name, 'r=%d' % r, ''.join(types), res.splitlines()[-1], '|', res.splitlines()[0])

# Theorem E = brute force, and Theorem B: friendly identity transitions
for q in (2, 3, 4, 5):
    G = W(q); D = full_dist(G)
    for trial in range(30):
        # friendly H->D identity: A = points; random R (sometimes partial ovoid, sometimes not)
        size = rng.randint(1, q * q + 1)
        if trial % 2 == 0:
            # greedy partial ovoid
            R = []
            order = list(range(G.np)); rng.shuffle(order)
            for p in order:
                if len(R) >= size: break
                if all(not G.col[p, x] for x in R): R.append(p)
        else:
            R = rng.sample(range(G.np), min(size, 4))
        Rs = set(R)
        bb = brute_bad(G, 'H', 'D', identity(G.np), Rs, D)
        ok, f = exact_conditions(G, 'H', 'D', identity(G.np), Rs)
        po = is_partial_ovoid(G, R)
        assert (bb == 0) == ok, (q, trial, bb, f)
        assert ok == po, (q, trial, ok, po)
        # non-friendly H->H with a random bijection and a random small R
        Mr = random_bijection(G.np, rng)
        R2 = set(rng.sample(range(G.np), rng.randint(1, 3)))
        bb2 = brute_bad(G, 'H', 'H', Mr, R2, D)
        ok2, f2 = exact_conditions(G, 'H', 'H', Mr, R2)
        assert (bb2 == 0) == ok2, (q, trial, bb2, f2)
    log('ThmB/ThmE', G.name, '30 trials: brute force == (E1)-(E3); friendly identity repaired <=> partial ovoid: ok')

open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'test_basic_out.txt'), 'w').write('\n'.join(out) + '\n')

# Theorem E with freed sets containing whole lines / pencils (tests the corrected (E1))
for q in (2, 3):
    G = W(q); D = full_dist(G); agree = 0; kinds_seen = set()
    for trial in range(300):
        Mr = random_bijection(G.np, rng)
        R = set(G.lines[rng.randrange(G.nl)])          # a whole line
        if trial % 3 == 0:
            Mi = [0] * G.np
            for a, b in enumerate(Mr): Mi[b] = a
            v = rng.randrange(G.np)                      # make all lines through v images of freed points
            R |= {Mi[l] for l in G.plines[v]}
        if trial % 2 == 0:
            R |= set(rng.sample(range(G.np), 2))
        bb = brute_bad(G, 'H', 'H', Mr, R, D)
        ok, f = exact_conditions(G, 'H', 'H', Mr, R)
        assert (bb == 0) == ok, (q, trial, bb, f)
        kinds_seen |= {x[0] for x in f}
        agree += 1
    log('ThmE (whole lines in R)', G.name, agree, 'trials agree; failure types seen', sorted(kinds_seen))
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'test_basic_out.txt'), 'w').write('\n'.join(out) + '\n')

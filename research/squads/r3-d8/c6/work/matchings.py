"""Build hop matchings for variants A (two dualities), B (duality + random), C (two random).
Each hop is a bijection points->lines s(p) (line index in 0..N-1) with s(p) not incident to p, and the two hops share no pair.
Output: matchings file 'J N' then J rows of N ints."""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh

W = '/home/user/degree-diameter/research/squads/r3-d8/c6/work'
H = gh.load(3)
N = H.N
H_nb = [set() for _ in range(N)]
for k in range(N):
    for p in H.lines[k]:
        H_nb[int(p)].add(k)
duals = np.load(os.path.join(W, 'duals_points.npy'))


def bad(s, p, other=None):
    return s[p] in H_nb[p] or (other is not None and other[p] == s[p])


def repair(s, other=None):
    """swap targets of absolute points (flag clash) with a partner point, keeping a bijection"""
    s = s.copy()
    for p in range(N):
        if not bad(s, p, other):
            continue
        for q in range(N):
            if q == p:
                continue
            t = s.copy(); t[p], t[q] = s[q], s[p]
            if not bad(t, p, other) and not bad(t, q, other):
                s = t
                break
        else:
            raise RuntimeError('no repair')
    return s


def nonincident_bijection(rng, avoid_list):
    for _ in range(1000000):
        perm = rng.permutation(N)
        if all(not bad(perm, p) and all(perm[p] != a[p] for a in avoid_list) for p in range(N)):
            return perm
    raise RuntimeError('no random bijection')


def write(path, hops):
    with open(path, 'w') as fh:
        fh.write(f'{len(hops)} {N}\n')
        for h in hops:
            fh.write(' '.join(str(int(x)) for x in h) + '\n')


# variant A: duality pair (s1, s3) with no shared pairs; repair absolute points
a1 = repair(duals[0])
a2 = repair(duals[2], other=a1)
assert all(not bad(a1, p) for p in range(N)) and all(not bad(a2, p, a1) for p in range(N))
assert len(set(a1.tolist())) == N and len(set(a2.tolist())) == N
write(os.path.join(W, 'hopsA.txt'), [a1, a2])
print('A written; repaired pairs changed points:', int((a1 != duals[0]).sum()), int((a2 != duals[2]).sum()))

# variant B: duality s1 (repaired) + random non-incident matching; seeds 1..3 saved for later use
for seed in (1, 2, 3):
    rng = np.random.default_rng(1000 + seed)
    r = nonincident_bijection(rng, [a1])
    write(os.path.join(W, f'hopsB_s{seed}.txt'), [a1, r])
    # variant C: two random non-incident matchings (seed matched to B)
    rng = np.random.default_rng(2000 + seed)
    c1 = nonincident_bijection(rng, [])
    c2 = nonincident_bijection(rng, [c1])
    write(os.path.join(W, f'hopsC_s{seed}.txt'), [c1, c2])
print('B, C written')

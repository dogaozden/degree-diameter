# c14: search for S (e in S) with (S^-1 S)^t = G but (S S^-1)^t != G, or the reverse.
import random, itertools, sys
from check_sets import perm_mul, quat_mul, sl23_mul, closure_group

def dihedral(n):
    r = tuple((i+1) % n for i in range(n)); f = tuple((-i) % n for i in range(n))
    return closure_group([r, f], perm_mul, tuple(range(n)))

def sym(n):
    gens = [tuple([1,0]+list(range(2,n))), tuple(list(range(1,n))+[0])]
    return closure_group(gens, perm_mul, tuple(range(n)))

def psl27():
    # PSL(2,7) acting on 8 points of projective line over F7: x->x+1, x->2x, x->-1/x
    def inv(a): return pow(a, 5, 7)
    pts = list(range(8))  # 7 = infinity
    def mob(f):
        return tuple(f(x) for x in pts)
    INF = 7
    t = mob(lambda x: INF if x == INF else (x+1) % 7)
    m = mob(lambda x: INF if x == INF else (2*x) % 7)
    s = mob(lambda x: 0 if x == INF else (INF if x == 0 else (-inv(x)) % 7))
    return closure_group([t, m, s], perm_mul, tuple(range(8)))

def run(name, G, mul, trials, rng):
    n = len(G)
    idx = {g: i for i, g in enumerate(G)}
    M = [[idx[mul(a, b)] for b in G] for a in G]
    ident = next(i for i in range(n) if all(M[i][j] == j for j in range(n)))
    inv = [next(j for j in range(n) if M[i][j] == ident) for i in range(n)]
    def sm(X, Y): return {M[x][y] for x in X for y in Y}
    found = []
    for _ in range(trials):
        k = rng.randint(2, 7)
        if k - 1 > n - 1: continue
        S = {ident} | set(rng.sample([i for i in range(n) if i != ident], k-1))
        X = sm({inv[s] for s in S}, S); Y = sm(S, {inv[s] for s in S})
        Xt = {ident}; Yt = {ident}
        for t in range(1, 5):
            Xt = sm(Xt, X); Yt = sm(Yt, Y)
            c1 = len(Xt) == n; c2 = len(Yt) == n
            if c1 != c2:
                found.append((t, len(S), sorted(S), 'S^-1S covers' if c1 else 'SS^-1 covers'))
                break
            if c1 and c2:
                break
    return found

if __name__ == '__main__':
    rng = random.Random(1)
    groups = {
        'D5': (dihedral(5), perm_mul), 'D6': (dihedral(6), perm_mul), 'S4': (sym(4), perm_mul),
        'D7': (dihedral(7), perm_mul), 'A4': (closure_group([(1,2,0,3),(1,0,3,2)], perm_mul, (0,1,2,3)), perm_mul),
        'SL23': (closure_group([(1,1,0,1),(0,2,1,0),(1,0,0,1)], sl23_mul, (1,0,0,1)), sl23_mul),
        'PSL27': (psl27(), perm_mul),
    }
    for name, (G, mul) in groups.items():
        f = run(name, G, mul, 3000, rng)
        print(name, 'order', len(G), 'one-sided hits', len(f), f[:3])
        sys.stdout.flush()

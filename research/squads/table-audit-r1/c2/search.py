#!/usr/bin/env python3
"""Card c2: cubic bipartite Cayley graphs Cay(G,S), |S|=3, S=S^-1, bipartite via S in odd coset.

Groups: A x| Z_k with A = Z_m1 x Z_m2 and Z_k acting by diag(s1, s2) (covers metacyclic, dihedral,
generalized dihedral (s=-1), direct products with a cyclic/abelian factor). Vertex-transitive, so the
diameter is the eccentricity of the identity (BFS from vertex 0). Bipartite iff BFS levels alternate parity on edges.
Usage: python3 search.py OUTDIR SECONDS_PER_GROUP CAP_PER_ORDER ORDER [ORDER ...]
"""
import sys, time, random, os, json
import numpy as np

def table(m1, m2, k, s1, s2):
    N = m1 * m2 * k
    idx = np.arange(N)
    a = idx // (m2 * k); b = (idx // k) % m2; j = idx % k
    s1p = np.array([pow(s1, t, m1) if m1 > 1 else 0 for t in range(k)], dtype=np.int64)
    s2p = np.array([pow(s2, t, m2) if m2 > 1 else 0 for t in range(k)], dtype=np.int64)
    A1, B1, J1 = a[:, None], b[:, None], j[:, None]
    A2, B2, J2 = a[None, :], b[None, :], j[None, :]
    na = (A1 + s1p[J1] * A2) % m1 if m1 > 1 else np.zeros((N, N), dtype=np.int64)
    nb = (B1 + s2p[J1] * B2) % m2 if m2 > 1 else np.zeros((N, N), dtype=np.int64)
    nj = (J1 + J2) % k
    return (na * (m2 * k) + nb * k + nj).astype(np.int32)

def valid_action(m, s, k):
    return (m == 1) or (pow(s, k, m) == 1 % m and np.gcd(s, m) == 1)

def check_group(T, rng, trials=3000):
    N = T.shape[0]
    for _ in range(trials):
        x, y, z = rng.randrange(N), rng.randrange(N), rng.randrange(N)
        if T[T[x, y], z] != T[x, T[y, z]]:
            return False
    return all(T[0, x] == x and T[x, 0] == x for x in range(N))

def evaluate(T, S, N):
    lev = np.full(N, -1, dtype=np.int64); lev[0] = 0
    frontier = np.array([0]); d = 0
    Sa = np.array(S)
    while frontier.size:
        nb = np.unique(T[frontier][:, Sa].ravel())
        nb = nb[lev[nb] < 0]
        if nb.size == 0:
            break
        d += 1; lev[nb] = d; frontier = nb
    if (lev < 0).any():
        return None
    par = lev & 1
    for s in S:
        if np.any(par[T[:, s]] == par):
            return None
    return int(lev.max())

def search(T, inv, rng, budget):
    N = T.shape[0]
    invol = [x for x in range(1, N) if inv[x] == x]
    noninv = [x for x in range(1, N) if inv[x] != x]
    best = (10 ** 9, None)
    t0 = time.time(); tries = 0
    def random_S():
        if len(invol) >= 3 and (not noninv or rng.random() < 0.5):
            S = rng.sample(invol, 3)
        elif invol and noninv:
            t = rng.choice(invol); g = rng.choice(noninv); S = [t, g, int(inv[g])]
        else:
            return None
        return S if len(set(S)) == 3 and 0 not in S else None
    def mutate(S):
        S = list(S)
        if all(inv[x] == x for x in S):
            i = rng.randrange(3); c = rng.choice(invol)
            S[i] = c
        else:
            ti = [i for i in range(3) if inv[S[i]] == S[i]][0]
            if rng.random() < 0.5:
                S[ti] = rng.choice(invol)
            else:
                g = rng.choice(noninv); S = [S[ti], g, int(inv[g])]
                S[0], S[ti] = S[ti], S[0]
        return S if len(set(S)) == 3 and 0 not in S else None
    while time.time() - t0 < budget:
        tries += 1
        S = None
        if best[1] is not None and rng.random() < 0.6:
            S = mutate(best[1])
        if S is None:
            S = random_S()
        if S is None:
            continue
        d = evaluate(T, S, N)
        if d is not None and d <= best[0]:
            best = (d, sorted(S))
    return best, tries

def groups_for(N, cap, rng):
    cands = []
    divs = [k for k in range(1, N + 1) if N % k == 0]
    for k in divs:
        m = N // k
        if m < 2:
            continue
        if k == 1:
            cands.append((m, 1, 1, 1, 1)); continue
        R = [r for r in range(1, m) if np.gcd(r, m) == 1 and pow(r, k, m) == 1 % m] if m > 2 else [1]
        for r in R:
            cands.append((m, 1, k, r, 1))
    for m1 in range(2, N + 1):
        if N % m1:
            continue
        for m2 in range(m1, N + 1):
            if (N // m1) % m2:
                continue
            k = N // (m1 * m2)
            if k < 2:
                continue
            U1 = [s for s in range(1, m1) if np.gcd(s, m1) == 1 and pow(s, k, m1) == 1 % m1] if m1 > 2 else [1]
            U2 = [s for s in range(1, m2) if np.gcd(s, m2) == 1 and pow(s, k, m2) == 1 % m2] if m2 > 2 else [1]
            combos = [(s1, s2) for s1 in U1 for s2 in U2]
            rng.shuffle(combos)
            for s1, s2 in combos[:6]:
                cands.append((m1, m2, k, s1, s2))
    rng.shuffle(cands)
    # keep dihedral-type actions (s=-1) first in the order of preference
    pref = [c for c in cands if (c[3] == c[0] - 1 or c[4] == c[1] - 1) and c[2] == 2]
    rest = [c for c in cands if c not in pref]
    return (pref + rest)[:cap]

def edges_of(T, S, N):
    E = set()
    for g in range(N):
        for s in S:
            h = int(T[g, s]); E.add((min(g, h), max(g, h)))
    return sorted(E)

def main():
    outdir = sys.argv[1]; budget = float(sys.argv[2]); cap = int(sys.argv[3])
    orders = [int(x) for x in sys.argv[4:]]
    rng = random.Random(12345)
    os.makedirs(outdir, exist_ok=True)
    log = open(os.path.join(outdir, 'search_log.txt'), 'a')
    for N in orders:
        best_overall = None
        glist = groups_for(N, cap, rng)
        print(f"# N={N} groups={len(glist)}", flush=True)
        for (m1, m2, k, s1, s2) in glist:
            T = table(m1, m2, k, s1, s2)
            assert T.shape[0] == N
            if not check_group(T, rng):
                print("GROUP AXIOM FAIL", m1, m2, k, s1, s2, flush=True); continue
            inv = np.argmax(T == 0, axis=1)
            (d, S), tries = search(T, inv, rng, budget)
            name = f"A=Z{m1}xZ{m2} x| Z{k} diag({s1},{s2})"
            line = f"N={N} {name} best_diam={d if S else None} S={S} tries={tries}"
            print(line, flush=True); log.write(line + "\n"); log.flush()
            if S is not None and (best_overall is None or d < best_overall[0]):
                best_overall = (d, (m1, m2, k, s1, s2), S)
        if best_overall:
            d, params, S = best_overall
            T = table(*params)
            E = edges_of(T, S, N)
            path = os.path.join(outdir, f"best_N{N}_diam{d}.txt")
            with open(path, 'w') as f:
                f.write(f"{N}\n" + "".join(f"{u} {v}\n" for u, v in E))
            print(f"BEST N={N} diam={d} group={params} S={S} edges={len(E)} file={path}", flush=True)
    log.close()

if __name__ == '__main__':
    main()

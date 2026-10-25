#!/usr/bin/env python3
"""Card c4: base-design comparison and annealing for cyclic lifts of B = incidence(H(5)) + 2 extra edges per vertex.

Usage:
  python3 bcd4.py compare            # designs a..e at M = 20, 22, 5 voltage draws each
  python3 bcd4.py anneal DESIGN M SECONDS SEED   # anneal voltage orbits starting from the best compare draw
"""
import os, sys, time, subprocess, math, json
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs

HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.join(HERE, 'work')
os.makedirs(WORK, exist_ok=True)
H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin', '/tmp/bcdt/hex/singer_q5.bin')
N, q, KA = H.N, H.q, H.KA
NO = len(H.prep)
Q1 = q + 1
TL = np.empty((KA, N), dtype=np.int64)
TL[0] = np.arange(N)
for t in range(1, KA):
    TL[t] = H.tl[TL[t - 1]]
RP, LR, PO, PE, PL = H.prep, H.lrep, H.porb, H.ppos, H.plines


def bfs_lines(p0):
    """distance in the incidence graph from point p0 to every line"""
    dp = np.full(N, -1); dl = np.full(N, -1)
    dp[p0] = 0; fp = [p0]; d = 0
    while fp:
        fl = []
        for p in fp:
            for L in PL[p]:
                if dl[L] < 0:
                    dl[L] = d + 1; fl.append(L)
        fp = []
        for L in fl:
            for p in H.lines[L]:
                if dp[p] < 0:
                    dp[p] = d + 2; fp.append(p)
        d += 2
    assert (dl >= 0).all()
    return dl


DL = np.array([bfs_lines(p) for p in RP])  # NO x N: distance from point rep to every line
assert set(np.unique(DL).tolist()) == {1, 3, 5}

# slot of each incidence edge (p, PL[p,k]) in the rep's line list (voltage parameter index)
_L0 = TL[((KA - PE) % KA)[:, None], PL]                     # tau^-e L for each incidence
_repl = PL[RP[PO]]                                          # rep's lines for each point
FS = (_repl[:, None, :] == _L0[:, :, None]).argmax(axis=2)  # N x Q1
assert (_repl[np.arange(N)[:, None], FS] == _L0).all()


def perfect_matching(adj, rng):
    matchR = -np.ones(NO, dtype=np.int64); matchL = -np.ones(NO, dtype=np.int64)

    def aug(u, seen):
        for v in rng.permutation(adj[u]):
            if not seen[v]:
                seen[v] = True
                if matchR[v] < 0 or aug(matchR[v], seen):
                    matchR[v] = u; matchL[u] = v
                    return True
        return False

    for u in rng.permutation(NO):
        if not aug(u, np.zeros(NO, dtype=bool)):
            return None
    return matchL


def orbit_bijection(rng, ok):
    """ok[o, t, j]: point-orbit rep o may go to tau^t(lrep[j]). Returns an equivariant bijection points -> lines."""
    adj = [np.nonzero(ok[o].any(axis=0))[0] for o in range(NO)]
    pi = perfect_matching(adj, rng)
    if pi is None:
        return None
    T = np.array([rng.choice(np.nonzero(ok[o, :, pi[o]])[0]) for o in range(NO)])
    return TL[(PE + T[PO]) % KA, LR[pi[PO]]]


def sig_dist(rng, d):
    ok = (DL[:, TL[:, LR]] == d)  # NO x KA x NO
    s = orbit_bijection(rng, ok)
    if s is None:
        raise RuntimeError(f'no equivariant bijection at distance {d}')
    # check: every point maps to a line at distance d
    dd = DL[PO, TL[(KA - PE) % KA, s]]
    assert (dd == d).all()
    return s


def build_design(name, rng):
    if name == 'a':
        return [hs.equivariant_bijection(H, rng), hs.equivariant_bijection(H, rng)]
    if name == 'b':
        s = hs.equivariant_bijection(H, rng)
        return [s, s.copy()]
    if name.startswith('c'):
        c = int(name[1:]); s = hs.equivariant_bijection(H, rng)
        return [s, TL[c][s]]
    if name.startswith('d'):
        d = int(name[1:])
        return [sig_dist(rng, d), sig_dist(rng, d)]
    if name == 'e':
        return [hs.equivariant_bijection(H, rng), sig_dist(rng, 1)]
    raise ValueError(name)


def build_edges(sigs):
    U = [np.repeat(np.arange(N), Q1)]; V = [N + PL.ravel()]; I = [(PO[:, None] * Q1 + FS).ravel()]
    for j, s in enumerate(sigs):
        U.append(np.arange(N)); V.append(N + s); I.append(NO * Q1 + j * NO + PO)
    return np.concatenate(U), np.concatenate(V), np.concatenate(I)


def orbit_conflict(X, o, M, nsig):
    """True if the voltages of orbit o create two base edges between the same pair with equal voltage"""
    r = RP[o]
    lines = [int(X[NO * Q1 + j * NO + o]) for j in range(nsig)]
    sig_lines = [int(LINES[j][r]) for j in range(nsig)]
    for j in range(nsig):
        for s in range(Q1):
            if sig_lines[j] == PL[r, s] and lines[j] == X[o * Q1 + s]:
                return True
        for k in range(j):
            if sig_lines[j] == sig_lines[k] and lines[j] == lines[k]:
                return True
    return False


LINES = None


def sample_X(rng, M, sigs):
    global LINES
    LINES = sigs
    nsig = len(sigs)
    X = np.zeros(NO * Q1 + nsig * NO, dtype=np.int64)
    X[:NO * Q1] = rng.integers(0, M, NO * Q1)
    for o in range(NO):
        r = RP[o]
        while True:
            vals = rng.integers(0, M, nsig)
            for j in range(nsig):
                X[NO * Q1 + j * NO + o] = vals[j]
            if not orbit_conflict(X, o, M, nsig):
                break
    return X


def write_spec(path, M, U, V, A):
    with open(path, 'w') as f:
        f.write(f"bcd-lift 1\ngroup cyclic {M}\nvertices {2 * N}\nedges {len(U)}\n")
        f.write(''.join(f"{u} {v} {a}\n" for u, v, a in zip(U.tolist(), V.tolist(), A.tolist())))
        f.write("aut 1\n" + " ".join(map(str, H.base_tau())) + "\n" + " ".join(["0"] * (2 * N)) + "\n")
        f.write("end\n")


ENV = dict(os.environ, OMP_NUM_THREADS='1')


def cost_file(path):
    out = subprocess.run(['/tmp/bcd', 'lift', path, '8', '8', '--cost', '--threads', '1'],
                         capture_output=True, text=True, env=ENV)
    for ln in out.stdout.splitlines():
        if ln.startswith('COST'):
            return int(ln.split()[1])
    raise RuntimeError(out.stdout + out.stderr)


def cost_of(sigs, X, M, path):
    U, V, I = build_edges(sigs)
    write_spec(path, M, U, V, X[I] % M)
    return cost_file(path)


def compare(Ms=(20, 22), draws=5, designs=('a', 'b', 'c1', 'c2', 'c15', 'd1', 'd3', 'd5', 'e')):
    global LINES
    results = {}
    for name in designs:
        for M in Ms:
            costs = []; best = None
            for k in range(draws):
                rng = np.random.default_rng([k, M, 20251025])
                sigs = build_design(name, rng)
                LINES = sigs
                X = sample_X(rng, M, sigs)
                path = os.path.join(WORK, f'cmp_{name}_M{M}_{k}.spec')
                c = cost_of(sigs, X, M, path)
                os.remove(path)
                costs.append(c)
                if best is None or c < best[0]:
                    best = (c, sigs, X)
            np.savez(os.path.join(WORK, f'best_{name}_M{M}.npz'), sigs=np.array(best[1]), X=best[2], M=M,
                     cost=best[0])
            results[f'{name}_M{M}'] = {'costs': costs, 'mean': float(np.mean(costs)), 'min': int(min(costs))}
            print(name, M, costs, 'mean %.2f' % np.mean(costs), flush=True)
    with open(os.path.join(HERE, 'compare.json'), 'w') as f:
        json.dump(results, f, indent=1)
    return results


def anneal(name, M, seconds, seed, T0=1.5):
    global LINES
    npz = os.path.join(WORK, f'best_{name}_M{M}.npz')
    rng = np.random.default_rng(seed)
    if os.path.exists(npz):
        d = np.load(npz)
        sigs = [np.array(s) for s in d['sigs']]
        X = np.array(d['X']).astype(np.int64)
    else:
        raise SystemExit('no compare result for ' + name)
    LINES = sigs
    nsig = len(sigs)
    U, V, I = build_edges(sigs)
    path = os.path.join(WORK, f'anneal_{name}_M{M}_{seed}.spec')
    cur = X.copy(); curc = cost_of(sigs, cur, M, path)
    best = cur.copy(); bestc = curc
    print('start', curc, flush=True)
    t0 = time.time(); it = 0; acc = 0; nparam = len(cur)
    log = []
    while time.time() - t0 < seconds and bestc > 0:
        frac = (time.time() - t0) / seconds
        T = max(0.05, T0 * (1 - frac))
        k = int(rng.integers(nparam)); old = cur[k]
        new = int(rng.integers(M))
        if new == old:
            continue
        cur[k] = new
        if k < NO * Q1:
            o = k // Q1
        else:
            o = (k - NO * Q1) % NO
        if orbit_conflict(cur, o, M, nsig):
            cur[k] = old
            continue
        c = cost_of(sigs, cur, M, path)
        it += 1
        dlt = c - curc
        if dlt <= 0 or rng.random() < math.exp(-dlt / T):
            curc = c; acc += 1
            if c < bestc:
                bestc = c; best = cur.copy()
                print('  it %d t %.0f best %d' % (it, time.time() - t0, bestc), flush=True)
        else:
            cur[k] = old
    out = os.path.join(WORK, f'anneal_{name}_M{M}_{seed}.npz')
    np.savez(out, sigs=np.array(sigs), X=best, M=M, cost=bestc)
    print('done it=%d acc=%d best=%d time=%.0f' % (it, acc, bestc, time.time() - t0), flush=True)
    return bestc, out


if __name__ == '__main__':
    if sys.argv[1] == 'compare':
        compare()
    elif sys.argv[1] == 'anneal':
        anneal(sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]))

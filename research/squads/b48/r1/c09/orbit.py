# c09: orbit sets S = {e, x, s(x), s^2(x)} for an automorphism s of order 3 of a group G (Haar graph of the dipole).
# Automorphisms: (i) scalings (t,j)->(u t, j) on metacyclic Z_m x|_r Z_k with u^3 = 1 mod m, u != 1;
#                (ii) inner automorphisms conj by g with g^3 central, g non-central.
# Every x (orbit-minimal, x != e) is scored with `lift BASE GROUP.bin 4 8 eval`.
import sys, os, subprocess, time, json, math
import numpy as np

TD = '/home/user/degree-diameter/research/squads/b48/tools'
HERE = '/home/user/degree-diameter/research/squads/b48/r1/c09'
BASE = TD + '/bases/dipole4.txt'
LIFT = TD + '/lift'
BIN = HERE + '/bins/g.bin'

def meta_table(m, k, r):
    N = m * k
    rp = np.empty(k, dtype=np.int64); v = 1
    for j in range(k):
        rp[j] = v; v = v * r % m
    idx = np.arange(N)
    t = idx % m; j = idx // m
    T = (t[:, None] + rp[j][:, None] * t[None, :]) % m + m * ((j[:, None] + j[None, :]) % k)
    return T.astype(np.int64)

def is_aut(T, s):
    return np.array_equal(T[np.ix_(s, s)], s[T])

def perm_inv(s):
    inv = np.empty_like(s); inv[s] = np.arange(len(s)); return inv

def group_info(T):
    N = T.shape[0]
    ar = np.arange(N)
    central = (T == T.T).all(axis=1)
    inv = np.argmax(T == 0, axis=1)
    return central, inv

def order3_autos(T, m=None, k=None, maxconj=4):
    N = T.shape[0]; ar = np.arange(N)
    central, inv = group_info(T)
    out = []
    seen = set()
    def add(s, kind):
        s3 = s[s[s]]
        if not np.array_equal(s3, ar) or np.array_equal(s, ar):
            return
        key = min(s.tobytes(), perm_inv(s).tobytes())
        if key in seen: return
        seen.add(key); out.append((kind, s))
    if m is not None:
        t = ar % m; j = ar // m
        for u in range(2, m):
            if math.gcd(u, m) == 1 and pow(u, 3, m) == 1:
                s = (u * t % m) + m * j
                if is_aut(T, s): add(s, 'scale%d' % u)
    g2 = T[ar, ar]; g3 = T[g2, ar]
    cands = np.nonzero(central[g3] & ~central)[0]
    cnt = 0
    for g in cands:
        if cnt >= maxconj: break
        s = T[T[g, ar], inv[g]]   # conjugation: always an automorphism
        key = min(s.tobytes(), perm_inv(s).tobytes())
        if key in seen: continue
        before = len(out)
        add(s, 'conj%d' % g)
        if len(out) > before: cnt += 1
    return out

def write_bin(T):
    N = T.shape[0]
    with open(BIN, 'wb') as f:
        f.write(np.int32(N).tobytes())
        f.write(T.astype('<u2').tobytes())

def score_orbit(T, s, cands):
    """Score all orbit-minimal x; return list of (cost, x)."""
    N = T.shape[0]
    ar = np.arange(N)
    s2 = s[s]
    xs = [x for x in range(1, N) if s[x] != x and x < s[x] and x < s2[x]]
    lines = ["0 %d %d %d" % (x, s[x], s2[x]) for x in xs]
    if not lines: return []
    out = subprocess.run([LIFT, BASE, BIN, '4', '8', 'eval'], input="\n".join(lines) + "\n",
                         capture_output=True, text=True, timeout=110).stdout.split("\n")
    res = []
    for x, c in zip(xs, out):
        if c.strip() == 'invalid' or c.strip() == '': continue
        res.append((int(c), x))
    return res

def groups_meta(Nlo, Nhi):
    for N in range(Nlo, Nhi + 1):
        for k in range(2, N):
            if N % k: continue
            m = N // k
            if m < 2: continue
            seen = set()
            for r in range(2, m):
                if math.gcd(r, m) != 1 or pow(r, k, m) != 1: continue
                # canonical: smallest r' = r^j with gcd(j,k)=1
                canon = min(pow(r, j, m) for j in range(1, k + 1) if math.gcd(j, k) == 1)
                if canon in seen: continue
                seen.add(canon)
                yield (m, k, r)

if __name__ == '__main__':
    Nlo, Nhi, maxgroups = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    outp = HERE + '/results_%d_%d.jsonl' % (Nlo, Nhi)
    t0 = time.process_time()
    ng = 0; best_all = None
    with open(outp, 'w') as fo:
        for (m, k, r) in groups_meta(Nlo, Nhi):
            if ng >= maxgroups: break
            T = meta_table(m, k, r)
            # sanity on first group only
            if ng == 0:
                rng = np.random.default_rng(1)
                for _ in range(2000):
                    x, y, z = rng.integers(0, T.shape[0], 3)
                    assert T[T[x, y], z] == T[x, T[y, z]]
            autos = order3_autos(T, m=m, k=k)
            if not autos:
                continue
            write_bin(T)
            ng += 1
            for kind, s in autos:
                res = score_orbit(T, s, None)
                if not res: continue
                c, x = min(res)
                rec = dict(N=T.shape[0], m=m, k=k, r=r, kind=kind, cost=c, x=int(x),
                           S=[0, int(x), int(s[x]), int(s[s[x]])])
                fo.write(json.dumps(rec) + "\n")
                if best_all is None or (c, -rec['N']) < (best_all['cost'], -best_all['N']):
                    best_all = rec
                if c == 0: break
    print("groups_with_order3_aut", ng, "cpu", round(time.process_time() - t0, 1))
    print("BEST", json.dumps(best_all))

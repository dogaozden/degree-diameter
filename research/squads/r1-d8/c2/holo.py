"""Card c2 (quadratic holonomy): Z_5 x Z_k lifts of H(5) + 2 hops.

Flags (p, L) get the Z_k voltage F[lam_L(p)], where lam_L(p) in {0..Q-1, Q} is the parameter of p on L relative to two
fixed points a_L, b_L of L (p = a + lam*b projectively; lam=Q means p = b). Hops: random bijections s_1, s_2 with
Z_5 voltages 1, 2 and Z_k label 0 or random. Q = 5 (prime, so GF(5) arithmetic is mod 5).
"""
import collections
import random
import subprocess
import sys

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402

SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad'
LD = '/home/user/degree-diameter/research/theorems/d8/liftdiam'
Q = 5


def bfs(H, src):
    N = H.N
    dist = [-1] * (2 * N)
    dist[src] = 0
    dq = collections.deque([src])
    while dq:
        x = dq.popleft()
        nb = [N + int(L) for L in H.through[x]] if x < N else [int(p) for p in H.lines[x - N]]
        for y in nb:
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                dq.append(y)
    return dist


def normalize(v):
    for x in v:
        if x % Q:
            inv = pow(x, Q - 2, Q)
            return tuple((y * inv) % Q for y in v)
    raise ValueError('zero vector')


def frames(H, rule):
    """returns dict L -> (a, b) point ids on line L"""
    N = H.N
    out = {}
    if rule == 'first':
        for L in range(N):
            pts = sorted(int(p) for p in H.lines[L])
            out[L] = (pts[0], pts[1])
    elif rule == 'proj':  # a = projection of o1 onto L, b = projection of o2 onto L (other than a)
        d1, d2 = bfs(H, 0), bfs(H, 1)
        for L in range(N):
            pts = [int(p) for p in H.lines[L]]
            a = min(pts, key=lambda p: d1[p])
            assert sum(1 for p in pts if d1[p] == d1[a]) == 1, 'projection not unique'
            b = min((p for p in pts if p != a), key=lambda p: d2[p])
            out[L] = (a, b)
    else:
        raise ValueError(rule)
    return out


def lam_table(H, fr):
    """dict (p, L) -> lam in {0..Q-1, Q}; lam=Q means p == b"""
    P = [tuple(int(x) % Q for x in H.P[p]) for p in range(H.N)]
    lam = {}
    for L, (a, b) in fr.items():
        for p in map(int, H.lines[L]):
            if p == a:
                lam[(p, L)] = 0
            elif p == b:
                lam[(p, L)] = Q
            else:
                found = None
                for t in range(1, Q):
                    v = normalize([(P[a][i] + t * P[b][i]) % Q for i in range(7)])
                    if v == P[p]:
                        found = t
                        break
                assert found is not None, (p, L)
                lam[(p, L)] = found
    return lam


def build_and_score(H, lam, Fvals, k, seed, hop_label, path, step=1, D=8, threads=1):
    """Fvals: list of Q+1 values in Z_k indexed by lam. hop_label: 'zero' or 'rand'. Returns unreached."""
    N = H.N
    rng = random.Random(seed)
    edges = []
    for (p, L), t in lam.items():
        edges.append((p, N + L, 0, Fvals[t] % k))
    s1 = list(range(N)); rng.shuffle(s1)
    s2 = list(range(N)); rng.shuffle(s2)
    for p in range(N):
        l1 = rng.randrange(k) if hop_label == 'rand' else 0
        l2 = rng.randrange(k) if hop_label == 'rand' else 0
        edges.append((p, N + s1[p], 1, l1))
        edges.append((p, N + s2[p], 2, l2))
    gh.write_base(path, 2 * N, Q, k, edges)
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', LD, path, str(D), str(threads), str(step)],
                         capture_output=True, text=True).stdout
    return int(out.split('unreached_pairs')[1].split()[0]), out

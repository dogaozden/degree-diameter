import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over semidirect products Z_m x| Z_k2.
#
# New helper: lift edges are preserved by LEFT multiplication by the group, so
# the group acts regularly on each fibre. Diameter <= D is then equivalent to
# every base vertex's fibre-identity reaching all vertices within D, which needs
# only 2k BFS runs per evaluation instead of 2kG.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define ITERS 4000

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static int d, D, K, M, K2, R, G, N;
static long long pw[64];
static int perm[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int *adj, *dg, *dist, *qu;
static clock_t t0;
static double budget;

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

/* Element (a,b) coded as a*K2+b; (a,b)*(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long t = (pw[b] * c + a) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static void build_lift(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int j = 0; j < d; j++) {
        for (int i = 0; i < K; i++) {
            int u = i, v = K + perm[j][i], g = volt[j][i];
            for (int x = 0; x < G; x++) {
                int a = u * G + x, b = v * G + gmul(x, g);
                adj[a * d + dg[a]++] = b;
                adj[b * d + dg[b]++] = a;
            }
        }
    }
}

/* Number of (source, vertex) pairs at distance > D, over one source per base vertex. */
static long long eval(void) {
    build_lift();
    long long bad = 0;
    for (int s0 = 0; s0 < 2 * K; s0++) {
        int s = s0 * G;
        for (int v = 0; v < N; v++) dist[v] = -1;
        int h = 0, t = 0;
        qu[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int x = qu[h++];
            if (dist[x] >= D) continue;
            for (int e = 0; e < dg[x]; e++) {
                int y = adj[x * d + e];
                if (dist[y] < 0) {
                    dist[y] = dist[x] + 1;
                    qu[t++] = y;
                }
            }
        }
        bad += N - t;
    }
    return bad;
}

static void shuffle_perm(int j) {
    for (int i = 0; i < K; i++) perm[j][i] = i;
    for (int i = K - 1; i > 0; i--) {
        int r = rint_(i + 1);
        int t = perm[j][i];
        perm[j][i] = perm[j][r];
        perm[j][r] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long long seed = atoll(argv[3]);
    budget = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 1 || d > MAXD || K < 1 || K > MAXK || M < 1 || K2 < 1 || K2 > 60 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * K * G;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * R) % M;
    if ((pw[K2 - 1] * R) % M != 1 % M) { printf("0 0\n"); return 0; }

    adj = malloc(sizeof(int) * (size_t)N * d);
    dg = malloc(sizeof(int) * (size_t)N);
    dist = malloc(sizeof(int) * (size_t)N);
    qu = malloc(sizeof(int) * (size_t)N);

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    t0 = clock();
    int found = 0;
    while (!found && elapsed() < budget) {
        for (int j = 0; j < d; j++) {
            shuffle_perm(j);
            for (int i = 0; i < K; i++) volt[j][i] = rint_(G);
        }
        long long c = eval();
        for (int it = 0; it < ITERS && elapsed() < budget; it++) {
            if (c == 0) { found = 1; break; }
            int sv[MAXD][MAXK], sp[MAXD][MAXK];
            memcpy(sv, volt, sizeof volt);
            memcpy(sp, perm, sizeof perm);
            if (rint_(8) == 0) {
                shuffle_perm(rint_(d));
            } else {
                int nm = 1 + (rint_(3) == 0);
                for (int t = 0; t < nm; t++) volt[rint_(d)][rint_(K)] = rint_(G);
            }
            long long c2 = eval();
            if (c2 <= c || rint_(100) == 0) {
                c = c2;
            } else {
                memcpy(volt, sv, sizeof volt);
                memcpy(perm, sp, sizeof perm);
            }
        }
        if (c == 0) found = 1;
    }

    if (!found) { printf("0 0\n"); return 0; }

    build_lift();
    int nA = K * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)nA * d + 8);
    int cnt = 0;
    for (int a = 0; a < nA; a++) {
        int nb[MAXD];
        int c2 = 0;
        for (int e = 0; e < dg[a]; e++) {
            int y = adj[a * d + e];
            int dup = 0;
            for (int t = 0; t < c2; t++) if (nb[t] == y) { dup = 1; break; }
            if (!dup) nb[c2++] = y;
        }
        for (int t = 0; t < c2; t++) {
            E[2 * cnt] = a;
            E[2 * cnt + 1] = nb[t];
            cnt++;
        }
    }
    printf("%d %d\n", N, cnt);
    for (int i = 0; i < cnt; i++) printf("%d %d\n", E[2 * i], E[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane and generalized-quadrangle bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension (applied to PG, GQ and group-lift results).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover all vertices within radius D-1."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Group parameters and the C-backed lift search.
# ----------------------------------------------------------------------------

def _sample_params(G, rng):
    """Return (m, k2, r) with Z_m x|_r Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            return (m, 1, 1)
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return (m, k2, rng.choice(cands))
    return None


def _c_group(d, D, k, prm, seed, tl):
    """Run the C hill-climber for base size k in the given group. Returns (n, edges) or None."""
    m, k2, r = prm
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{tl:.2f}", k, m, k2, r],
                         timeout=tl + 10.0)
        n, e = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return None
    if n == 0 or not lib.is_valid(n, e, d, D):
        return None
    return n, e


# ----------------------------------------------------------------------------
# Haar graphs (kept as a secondary family for D = 3).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    ext_deadline = start + 0.4 * time_limit
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Algebraic bases, grown by cover extension.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, ext_deadline, rng)
            consider(n2, e2)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    # Main loop: C-backed group-lift search, with Haar graphs for D = 3 diversity.
    group_p = 0.9 if D >= 4 else 0.4
    group_sizes = [1, 2, 3, 4, 5, 6]
    state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 0.3:
            break
        if rng.random() < group_p:
            k = rng.choice(group_sizes)
            st = state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            prm = _sample_params(G, rng)
            if prm is None:
                st["G"] = G + 1
                continue
            slice_t = min(3.0, remaining)
            res = _c_group(d, D, k, prm, rng.randrange(1 << 30), slice_t)
            if res is not None:
                consider(res[0], res[1])
                # New idea in use: grow the fresh lift by cover vertices, then saturate.
                g_deadline = min(deadline, time.monotonic() + 1.5)
                n2, e2 = _grow(res[0], res[1], d, D, g_deadline, rng)
                consider(n2, e2)
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

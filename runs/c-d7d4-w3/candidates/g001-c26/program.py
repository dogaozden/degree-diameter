import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (semi-regular) lifts over small groups.
#
# Graph: A-vertices (i, x) and B-vertices (j, y), i < S, j < S, x, y in G.
# Each of S*DEG darts t = (i = t / DEG, j = dB[t], voltage g = dG[t]) gives
# edges A(i, x) -- B(j, x*g) for every x. Left multiplication by G is an
# automorphism that is transitive on each side's copies of a base vertex, so
# diameter <= DIAM holds iff every one of the 2S base vertices reaches the
# whole graph within DIAM steps. Annealing minimises the total number of
# unreached (source, vertex) pairs. Any zero-cost lift is valid.
# Groups: cyclic Z_G or semidirect Z_M x|_r Z_k with M*k = G, r^k = 1 mod M.
# Args: d D seed budget_seconds target_n. Only graphs with n > target_n are
# reported. Prints "n m" then m edges, or "0 0" when nothing was found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 5000
#define MAXDEG 16
#define MAXDARTS 128
#define MAXG 600
#define MAXOPT 4096

static int DEG = 3, DIAM = 2;
static int S = 1, G = 1, GM = 1, GK = 1, GR = 1;
static int NDART = 0;
static int dB[MAXDARTS], dG[MAXDARTS];
static int mulT[MAXG * MAXG];
static int pw[MAXG];
static int adj[MAXN][MAXDEG];
static int cnt[MAXN];
static int distv[MAXN];
static int que[MAXN];
static int eu[MAXN * MAXDEG], ev[MAXN * MAXDEG];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_sec(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void setup_group(int g, int M, int k, int r) {
    G = g;
    GM = M;
    GK = k;
    GR = r;
    for (int b = 0; b < k; b++) pw[b] = powmod(r, b, M);
    for (int x = 0; x < g; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < g; y++) {
            int c = y / k, e = y % k;
            int A = (a + pw[b] * c) % M;
            int B = (b + e) % k;
            mulT[x * g + y] = A * k + B;
        }
    }
}

static void random_init(void) {
    NDART = S * DEG;
    int t = 0;
    for (int j = 0; j < S; j++)
        for (int q = 0; q < DEG; q++) dB[t++] = j;
    for (int i = NDART - 1; i > 0; i--) {
        int k = rndint(i + 1);
        int tmp = dB[i];
        dB[i] = dB[k];
        dB[k] = tmp;
    }
    for (t = 0; t < NDART; t++) dG[t] = rndint(G);
}

static void build_adj(void) {
    int base = S * G;
    int n = 2 * S * G;
    for (int v = 0; v < n; v++) cnt[v] = 0;
    for (int i = 0; i < S; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int q = 0; q < DEG; q++) {
                int t = i * DEG + q;
                int w = base + dB[t] * G + mulT[x * G + dG[t]];
                adj[v][cnt[v]++] = w;
                adj[w][cnt[w]++] = v;
            }
        }
}

static int bfs_missing(int src, int n) {
    for (int v = 0; v < n; v++) distv[v] = -1;
    int head = 0, tail = 0;
    distv[src] = 0;
    que[tail++] = src;
    while (head < tail) {
        int u = que[head++];
        if (distv[u] >= DIAM) continue;
        for (int q = 0; q < DEG; q++) {
            int w = adj[u][q];
            if (distv[w] < 0) {
                distv[w] = distv[u] + 1;
                que[tail++] = w;
            }
        }
    }
    return n - tail;
}

static int total_cost(void) {
    int n = 2 * S * G;
    build_adj();
    int c = 0;
    for (int i = 0; i < S; i++) c += bfs_missing(i * G, n);
    for (int j = 0; j < S; j++) c += bfs_missing(S * G + j * G, n);
    return c;
}

static int anneal(double end, int *ok) {
    int cur = total_cost();
    double T = 2.0;
    long it = 0;
    while (cur > 0) {
        if ((it & 31) == 0 && now_sec() > end) break;
        it++;
        int type = rndint(3);
        if (type < 2) {
            int t = rndint(NDART);
            int old = dG[t];
            int nv = rndint(G);
            if (nv == old) continue;
            dG[t] = nv;
            int nc = total_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
            else dG[t] = old;
        } else {
            int t1 = rndint(NDART), t2 = rndint(NDART);
            if (dB[t1] == dB[t2]) continue;
            int tmp = dB[t1];
            dB[t1] = dB[t2];
            dB[t2] = tmp;
            int nc = total_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
            else {
                tmp = dB[t1];
                dB[t1] = dB[t2];
                dB[t2] = tmp;
            }
        }
        T *= 0.9995;
        if (T < 0.25) T = 2.0;
    }
    *ok = (cur == 0);
    return cur;
}

static int bS, bG, bM, bK, bR;
static int bdB[MAXDARTS], bdG[MAXDARTS];
static int optv[MAXOPT][3];

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int target = atoi(argv[5]);
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    if (DEG < 3 || DEG > MAXDEG || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    double end = now_sec() + budget;
    int bestN = target;
    int have = 0;

    while (now_sec() < end) {
        int s = 1 + rndint(4);
        if (s * DEG > MAXDARTS) continue;
        int Gmin = bestN / (2 * s) + 1;
        int g = Gmin + rndint(3);
        if (g < 2) g = 2;
        if (g > MAXG) continue;
        int nopt = 0;
        for (int k = 1; k <= g; k++) {
            if (g % k) continue;
            int M = g / k;
            if (M < 2) continue;
            for (int r = 1; r < M; r++) {
                if (gcd_i(r, M) != 1) continue;
                if (powmod(r, k, M) != 1 % M) continue;
                if (nopt < MAXOPT) {
                    optv[nopt][0] = M;
                    optv[nopt][1] = k;
                    optv[nopt][2] = r;
                    nopt++;
                }
            }
        }
        if (nopt == 0) continue;
        int pick = rndint(nopt);
        S = s;
        setup_group(g, optv[pick][0], optv[pick][1], optv[pick][2]);
        random_init();
        double slice_end = now_sec() + 2.5;
        if (slice_end > end) slice_end = end;
        int ok = 0;
        anneal(slice_end, &ok);
        if (ok) {
            int n = 2 * S * G;
            if (n > bestN) {
                bestN = n;
                have = 1;
                bS = S;
                bG = G;
                bM = GM;
                bK = GK;
                bR = GR;
                memcpy(bdB, dB, sizeof(dB));
                memcpy(bdG, dG, sizeof(dG));
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    S = bS;
    NDART = S * DEG;
    setup_group(bG, bM, bK, bR);
    memcpy(dB, bdB, sizeof(dB));
    memcpy(dG, bdG, sizeof(dG));
    int base = S * G;
    int m = 0;
    for (int i = 0; i < S; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int q = 0; q < DEG; q++) {
                int t = i * DEG + q;
                int w = base + dB[t] * G + mulT[x * G + dG[t]];
                int dup = 0;
                for (int q2 = 0; q2 < q; q2++) {
                    int t2 = i * DEG + q2;
                    int w2 = base + dB[t2] * G + mulT[x * G + dG[t2]];
                    if (w2 == w) {
                        dup = 1;
                        break;
                    }
                }
                if (!dup) {
                    eu[m] = v;
                    ev[m] = w;
                    m++;
                }
            }
        }
    printf("%d %d\n", 2 * S * G, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", eu[e], ev[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python).
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers: cover extension and edge saturation (Python).
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
    """Add vertices on the side opposite to c, each joined to a set of degree-spare vertices covering all."""
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
# Driver. Budget = 0.8 * time_limit.
#   1. Haar fallback (always valid).
#   2. Structured base (W(q) for D >= 4, PG(2,q) for D = 3), grown.
#   3. C bi-Cayley lift search for graphs above the current best order.
#   4. Cover-growth on the C result.
# Every kept graph passes lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase 1: structured base, grown.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        try:
            n0, e0 = base
            consider(n0, e0)
            grow_end = start + 0.2 * (deadline - start)
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)
        except Exception:
            pass

    # Phase 2: C bi-Cayley lift search above the current best order.
    if D >= 2 and d >= 3 and best_n < lib.moore_bound(d, D):
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            c_budget = 0.85 * remaining - 0.5
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=remaining * 0.95)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    # Phase 3: grow whatever is best now, if time remains.
    if D >= 2 and best_n < lib.moore_bound(d, D) and time.monotonic() < deadline:
        try:
            n3, e3 = _grow(best_n, best_e, d, D, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)

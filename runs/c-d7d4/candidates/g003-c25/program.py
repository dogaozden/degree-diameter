import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 6
#define MAXD 16
#define MAXG 700
#define MAXV 1400
#define MAXGL 8192
#define NBOUND 1300

static uint64_t rs = 88172645463325252ULL;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(nxt() % (uint64_t)n); }

static double rdbl(void) { return (double)(nxt() >> 11) / 9007199254740992.0; }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* Base graph: K A-vertices and K B-vertices, DEG perfect matchings (SIG[j]),
   voltages VOLT[j][i] in the group of order G. Lift vertex (i,x) -> i*G+x. */
static int D_, DEG, K, G, N;
static int MUL[MAXG * MAXG];
static int SIG[MAXD][MAXK];
static int VOLT[MAXD][MAXK];
static int ADJ[MAXV * MAXD];
static int CNT[MAXV];
static int DIST[MAXV];
static int QUE[MAXV];
static int BU[MAXV * MAXD];
static int BV[MAXV * MAXD];
static int BEST_N = 0, BEST_M = 0;

typedef struct { int m, k2, r; } Grp;
static Grp GL[MAXGL];
static int NGL = 0;

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect products Z_m x| Z_k2 of order g, element (a,b) coded as a*k2+b,
   (a,b)(c,d) = (a + r^b c, b + d); needs r^k2 = 1 mod m, gcd(r,m) = 1. */
static void enum_groups(int g) {
    NGL = 0;
    for (int k2 = 1; k2 <= g; k2++) {
        if (g % k2) continue;
        int m = g / k2;
        for (int r = 0; r < m; r++) {
            if (gcd_(r, m) != 1) continue;
            if (powmod_(r, k2, m) != (1 % m)) continue;
            if (NGL < MAXGL) {
                GL[NGL].m = m;
                GL[NGL].k2 = k2;
                GL[NGL].r = r;
                NGL++;
            }
        }
    }
}

static void build_mul(Grp gp) {
    int m = gp.m, k2 = gp.k2, r = gp.r;
    int pw[MAXG];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, d = y % k2;
            int a2 = (int)(((long)a + (long)pw[b] * c) % m);
            int b2 = (b + d) % k2;
            MUL[x * G + y] = a2 * k2 + b2;
        }
    }
}

static long build_graph(void) {
    N = 2 * K * G;
    for (int v = 0; v < N; v++) CNT[v] = 0;
    for (int i = 0; i < K; i++) {
        for (int x = 0; x < G; x++) {
            int a = i * G + x;
            for (int j = 0; j < DEG; j++) {
                int b = SIG[j][i];
                int w = (K + b) * G + MUL[x * G + VOLT[j][i]];
                ADJ[a * DEG + CNT[a]++] = w;
                ADJ[w * DEG + CNT[w]++] = a;
            }
        }
    }
    long dup = 0;
    for (int a = 0; a < K * G; a++) {
        int *p = &ADJ[a * DEG];
        for (int s = 0; s < DEG; s++)
            for (int t = s + 1; t < DEG; t++)
                if (p[s] == p[t]) dup++;
    }
    return dup;
}

/* Cost = (duplicate edges)*1000 + sum over base representatives of the number
   of vertices not within distance D. Fibre transitivity makes this exact. */
static long eval_cost(void) {
    long dup = build_graph();
    long cost = dup * 1000;
    for (int v = 0; v < 2 * K; v++) {
        int s = v * G;
        for (int t = 0; t < N; t++) DIST[t] = -1;
        int qh = 0, qt = 0;
        DIST[s] = 0;
        QUE[qt++] = s;
        while (qh < qt) {
            int u = QUE[qh++];
            if (DIST[u] >= D_) continue;
            for (int q = 0; q < DEG; q++) {
                int w = ADJ[u * DEG + q];
                if (DIST[w] < 0) {
                    DIST[w] = DIST[u] + 1;
                    QUE[qt++] = w;
                }
            }
        }
        cost += N - qt;
    }
    return cost;
}

static void store_best(void) {
    BEST_N = N;
    BEST_M = 0;
    for (int a = 0; a < K * G; a++) {
        for (int t = 0; t < DEG; t++) {
            BU[BEST_M] = a;
            BV[BEST_M] = ADJ[a * DEG + t];
            BEST_M++;
        }
    }
}

int main(int argc, char **argv) {
    {
        int ch;
        while ((ch = getchar()) != EOF) { }
    }
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], 0, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;

    if (d <= 2 || D_ < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;

    double s = 0.0, p = 1.0;
    for (int i = 0; i < D_; i++) {
        s += p;
        p *= (double)(d - 1);
        if (s > 1e9) break;
    }
    double bound = 2.0 * s;
    int NB = (bound > NBOUND) ? NBOUND : (int)bound;

    double endt = now_s() + budget;
    while (now_s() < endt) {
        if (BEST_N >= NB) break;
        K = 1 + rint_(4);
        int Gmin = BEST_N / (2 * K) + 1;
        if (Gmin < 2) Gmin = 2;
        int Gt = Gmin + rint_(3);
        int Gmax = NB / (2 * K);
        if (Gt > Gmax) Gt = Gmax;
        if (Gt < Gmin) continue;
        if (Gt > MAXG - 1) continue;
        G = Gt;
        enum_groups(G);
        if (NGL == 0) continue;
        Grp gp = GL[rint_(NGL)];
        build_mul(gp);

        for (int j = 0; j < DEG; j++) {
            for (int i = 0; i < K; i++) SIG[j][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int t = rint_(i + 1);
                int tmp = SIG[j][i];
                SIG[j][i] = SIG[j][t];
                SIG[j][t] = tmp;
            }
            for (int i = 0; i < K; i++) VOLT[j][i] = rint_(G);
        }

        long c = eval_cost();
        int iters = 3000;
        for (int it = 0; it < iters && c > 0; it++) {
            if ((it & 63) == 0 && now_s() >= endt) break;
            int j = rint_(DEG);
            int i = rint_(K);
            int old = VOLT[j][i];
            int nv = rint_(G);
            if (nv == old) continue;
            VOLT[j][i] = nv;
            long c2 = eval_cost();
            double T = 2.0 * (1.0 - (double)it / (double)iters) + 0.05;
            if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / T)) {
                c = c2;
            } else {
                VOLT[j][i] = old;
            }
        }
        if (c == 0) {
            int n = 2 * K * G;
            if (n > BEST_N) {
                build_graph();
                store_best();
            }
        }
    }

    if (BEST_M == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", BEST_N, BEST_M);
    for (int e = 0; e < BEST_M; e++) printf("%d %d\n", BU[e], BV[e]);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q), order 2(q+1)(q^2+1)."""
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


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the rest."""
    if D < 2:
        return n, edges
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
    """Alternate cover-vertex extension and edge saturation; both preserve diameter."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = start + 0.88 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact or structured bases for D = 3 and D = 4.
    if d >= 3 and D in (3, 4):
        base = None
        if D == 3:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    base = lib.projective_plane_incidence(q)
                    break
        else:
            for q in range(min(d - 1, 8), 1, -1):
                if lib.is_prime_power(q):
                    base = _gq_w(q)
                    break
        if base is not None:
            consider(base[0], base[1])
            if best[0] >= lib.moore_bound(d, D):
                return best
            # Cover growth gives a strong fallback; it gets a bounded share of time.
            n2, e2 = _grow(base[0], base[1], d, D, start + 0.3 * time_limit, rng)
            consider(n2, e2)
            if best[0] >= lib.moore_bound(d, D):
                return best

    # Main search: C engine over semidirect-product voltage lifts.
    remaining = total - time.monotonic() - 1.5
    if remaining > 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            timeout=remaining + 1.0)
            n3, e3 = lib.parse_graph_text(out)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

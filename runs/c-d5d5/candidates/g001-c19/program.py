"""Voltage-lift search for bipartite graphs with max degree d and diameter D.

Parent approach: Python hill-climbing over Z_m x| Z_k2 voltages.

New in this version:
  * The whole voltage search runs in C. Candidates are bi-Cayley / group lifts with
    k base vertices per side over metacyclic groups Z_m x| Z_k2 of order G.
  * Random restarts over metacyclic groups. Each run samples a divisor k2 of G and a
    root r with r^k2 = 1 (mod m), then anneals the layered voltages.
  * Layer-permutation moves: each layer of darts is a permutation, so swapping two
    B-targets inside one layer keeps every degree exact. Scalar voltage moves are
    mixed in as well.
  * Orbit-representative cost: left multiplication is an automorphism, so only 2k BFS
    runs (one per class representative) are needed. The cost is the count of
    unreached (representative, vertex) pairs at depth <= D.
  * The C engine verifies every improvement fully (degree, duplicates, bipartiteness,
    all-pairs diameter) before accepting it.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXT 256
#define MAXG 4096
#define MAXN (2 * 4 * MAXG)
#define BIG 1000000000LL

typedef struct { uint64_t s; } Rng;

static uint64_t rng_next(Rng *R) {
    uint64_t x = R->s;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    R->s = x;
    return x;
}
static int rng_int(Rng *R, int n) { return n <= 1 ? 0 : (int)(rng_next(R) % (uint64_t)n); }
static double rng_unit(Rng *R) { return (double)(rng_next(R) >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) { if (e & 1) r = r * x % m; x = x * x % m; e >>= 1; }
    return (int)r;
}

/* Current lift state: k base vertices per side, group Z_M x| Z_K2 of order G = M*K2,
   and T = k*d darts. Layer l holds darts l*k .. l*k+k-1; dart t has source index t%k. */
static int d_, D_, k_, G_, T_, M_, K2_;
static int PW_[MAXG];
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int *adjb, *cntb, *visb, *queb;
static int visstamp = 0;
static double t_stop;

/* Element x = a*K2 + b codes (a, b); (a,b)*(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int K = K2_, M = M_;
    int a = x / K, b = x - a * K;
    int c = y / K, e = y - c * K;
    int na = (a + (int)(((long long)PW_[b] * c) % M)) % M;
    int nb = (b + e) % K;
    return na * K + nb;
}

/* Random metacyclic group of order G: pick a divisor K2 of G and a root r. */
static void setup_group(Rng *R, int G) {
    int divs[64], nd = 0;
    int q;
    for (q = 1; q <= G && nd < 64; q++) if (G % q == 0) divs[nd++] = q;
    int k2 = divs[rng_int(R, nd)];
    int m = G / k2;
    int r = 1 % m;
    int tries;
    if (m >= 3 && k2 >= 2) {
        for (tries = 0; tries < 200; tries++) {
            int cand = 2 + rng_int(R, m - 2);
            if (gcd_i(cand, m) == 1 && powmod_i(cand, k2, m) == 1 % m) { r = cand; break; }
        }
    }
    M_ = m;
    K2_ = k2;
    PW_[0] = 1 % m;
    for (q = 1; q < k2; q++) PW_[q] = (int)((long long)PW_[q - 1] * r % m);
}

/* Random layered voltages: every layer is a permutation of the k B-targets. */
static void random_state(Rng *R) {
    int k = k_, d = d_, l, x, y, t;
    int perm[8];
    T_ = k * d;
    for (l = 0; l < d; l++) {
        for (x = 0; x < k; x++) perm[x] = x;
        for (x = k - 1; x > 0; x--) {
            y = rng_int(R, x + 1);
            int tmp = perm[x]; perm[x] = perm[y]; perm[y] = tmp;
        }
        for (x = 0; x < k; x++) {
            t = l * k + x;
            dI[t] = x;
            dJ[t] = perm[x];
            dS[t] = rng_int(R, G_);
        }
    }
}

/* Cost = number of (representative, vertex) pairs not within distance D. 0 means valid. */
static long long eval_cost(void) {
    const int k = k_, G = G_, d = d_, D = D_;
    const int N = 2 * k * G;
    int t, c, g, rr;
    for (t = 0; t < T_; t++)
        for (c = t + 1; c < T_; c++)
            if (dI[t] == dI[c] && dJ[t] == dJ[c] && dS[t] == dS[c]) return BIG;
    memset(cntb, 0, sizeof(int) * (size_t)N);
    for (t = 0; t < T_; t++) {
        int ib = dI[t] * G, jb = (k + dJ[t]) * G, s = dS[t];
        for (g = 0; g < G; g++) {
            int a = ib + g, b = jb + gmul(g, s);
            if (cntb[a] >= d || cntb[b] >= d) return BIG;
            adjb[(size_t)a * d + cntb[a]++] = b;
            adjb[(size_t)b * d + cntb[b]++] = a;
        }
    }
    long long unreached = 0;
    for (rr = 0; rr < 2 * k; rr++) {
        int src = rr * G;  /* representatives: A_i at i*G, B_j at (k+j)*G */
        int head = 0, tail = 0, lvl;
        if (++visstamp > 2000000000) { memset(visb, 0, sizeof(int) * MAXN); visstamp = 1; }
        queb[tail++] = src;
        visb[src] = visstamp;
        for (lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = queb[head++];
                const int *au = adjb + (size_t)u * d;
                for (c = 0; c < d; c++) {
                    int w = au[c];
                    if (visb[w] != visstamp) { visb[w] = visstamp; queb[tail++] = w; }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached;
}

static int mv_type, mv_t, mv_c, mv_olds;

static void apply_move(Rng *R) {
    if (k_ < 2 || rng_int(R, 2) == 0) {
        mv_type = 0;
        mv_t = rng_int(R, T_);
        mv_olds = dS[mv_t];
        dS[mv_t] = rng_int(R, G_);
    } else {
        mv_type = 1;
        int l = rng_int(R, d_);
        int x = rng_int(R, k_), y = rng_int(R, k_ - 1);
        if (y >= x) y++;
        mv_t = l * k_ + x;
        mv_c = l * k_ + y;
        int tmp = dJ[mv_t]; dJ[mv_t] = dJ[mv_c]; dJ[mv_c] = tmp;
    }
}

static void revert_move(void) {
    if (mv_type == 0) {
        dS[mv_t] = mv_olds;
    } else {
        int tmp = dJ[mv_t]; dJ[mv_t] = dJ[mv_c]; dJ[mv_c] = tmp;
    }
}

static long long anneal(Rng *R, int steps) {
    const double T0 = 3.0, T1 = 0.15;
    long long c = eval_cost();
    int st;
    for (st = 0; st < steps && c > 0; st++) {
        if ((st & 127) == 0 && now_s() > t_stop) break;
        double T = T0 * pow(T1 / T0, (double)st / (double)steps);
        apply_move(R);
        long long c2 = eval_cost();
        if (c2 <= c || rng_unit(R) < exp(-(double)(c2 - c) / T)) c = c2;
        else revert_move();
    }
    return c;
}

static int build_edges(int *eu, int *ev) {
    int k = k_, G = G_, t, g, idx = 0;
    for (t = 0; t < T_; t++) {
        int ib = dI[t] * G, jb = (k + dJ[t]) * G, s = dS[t];
        for (g = 0; g < G; g++) {
            eu[idx] = ib + g;
            ev[idx] = jb + gmul(g, s);
            idx++;
        }
    }
    return idx;
}

/* Full independent verification: ranges, degree, duplicates, bipartiteness, diameter. */
static int check_graph(int n, int m, const int *eu, const int *ev, int d, int D) {
    int ok = 0, i, j, u, s, head, tail;
    int *deg = NULL, *off = NULL, *pos = NULL, *adj = NULL;
    int *col = NULL, *dist = NULL, *q = NULL;
    if (n < 1 || m < 0) return 0;
    deg = calloc((size_t)n, sizeof(int));
    off = malloc(sizeof(int) * ((size_t)n + 1));
    pos = malloc(sizeof(int) * (size_t)n);
    adj = malloc(sizeof(int) * (2 * (size_t)m + 1));
    col = malloc(sizeof(int) * (size_t)n);
    dist = malloc(sizeof(int) * (size_t)n);
    q = malloc(sizeof(int) * (size_t)n);
    if (!deg || !off || !pos || !adj || !col || !dist || !q) goto done;
    for (i = 0; i < m; i++) {
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) goto done;
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (i = 0; i < n; i++) if (deg[i] > d) goto done;
    for (i = 0; i < m; i++)
        for (j = i + 1; j < m; j++)
            if ((eu[i] == eu[j] && ev[i] == ev[j]) || (eu[i] == ev[j] && ev[i] == eu[j])) goto done;
    off[0] = 0;
    for (i = 0; i < n; i++) { off[i + 1] = off[i] + deg[i]; pos[i] = off[i]; }
    for (i = 0; i < m; i++) {
        adj[pos[eu[i]]++] = ev[i];
        adj[pos[ev[i]]++] = eu[i];
    }
    for (i = 0; i < n; i++) col[i] = -1;
    for (s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        head = tail = 0;
        q[tail++] = s;
        while (head < tail) {
            u = q[head++];
            for (j = off[u]; j < off[u + 1]; j++) {
                int w = adj[j];
                if (col[w] < 0) { col[w] = col[u] ^ 1; q[tail++] = w; }
                else if (col[w] == col[u]) goto done;
            }
        }
    }
    for (s = 0; s < n; s++) {
        for (i = 0; i < n; i++) dist[i] = -1;
        dist[s] = 0;
        head = tail = 0;
        q[tail++] = s;
        while (head < tail) {
            u = q[head++];
            if (dist[u] >= D) continue;
            for (j = off[u]; j < off[u + 1]; j++) {
                int w = adj[j];
                if (dist[w] < 0) { dist[w] = dist[u] + 1; q[tail++] = w; }
            }
        }
        if (tail != n) goto done;
    }
    ok = 1;
done:
    free(deg); free(off); free(pos); free(adj);
    free(col); free(dist); free(q);
    return ok;
}

int main(int argc, char **argv) {
    int bn = 0, bm = 0, i, j;
    int *best_u = NULL, *best_v = NULL, best_n = 0, best_m = 0;
    Rng R;
    double tl, t_begin;
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    R.s = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (R.s == 0) R.s = 1;
    tl = atof(argv[4]);
    t_begin = now_s();
    t_stop = t_begin + (tl > 2.0 ? tl - 0.4 : tl * 0.6);

    if (scanf("%d %d", &bn, &bm) != 2 || bn <= 0 || bm < 0) { bn = 0; bm = 0; }
    if (bn > 0) {
        int ok = 1;
        best_u = malloc(sizeof(int) * (size_t)(bm + 1));
        best_v = malloc(sizeof(int) * (size_t)(bm + 1));
        for (i = 0; i < bm; i++) {
            if (scanf("%d %d", &best_u[i], &best_v[i]) != 2) { ok = 0; break; }
        }
        if (!ok) { bn = 0; bm = 0; }
    }
    best_n = bn;
    best_m = bm;

    if (d_ >= 3 && d_ <= 80 && D_ >= 2 && now_s() < t_stop) {
        adjb = malloc(sizeof(int) * (size_t)MAXN * (size_t)d_);
        cntb = malloc(sizeof(int) * MAXN);
        visb = calloc(MAXN, sizeof(int));
        queb = malloc(sizeof(int) * MAXN);
        int cap = 3 * d_ * MAXG + 16;
        int *eu = malloc(sizeof(int) * (size_t)cap);
        int *ev = malloc(sizeof(int) * (size_t)cap);
        const int ks[6] = {1, 1, 2, 2, 2, 3};

        while (now_s() < t_stop) {
            int k = ks[rng_int(&R, 6)];
            int target = best_n + 1;
            int Gmin = (target + 2 * k - 1) / (2 * k);
            if (Gmin < 2) Gmin = 2;
            int span = 1 + Gmin / 10;
            int G = Gmin + rng_int(&R, span);
            if (G > MAXG) G = MAXG;
            k_ = k;
            G_ = G;
            setup_group(&R, G);
            random_state(&R);
            long long c = anneal(&R, 4000);
            if (c == 0) {
                int m = build_edges(eu, ev);
                int n = 2 * k * G;
                if (n > best_n && check_graph(n, m, eu, ev, d_, D_)) {
                    int *nu = malloc(sizeof(int) * (size_t)(m + 1));
                    int *nv = malloc(sizeof(int) * (size_t)(m + 1));
                    memcpy(nu, eu, sizeof(int) * (size_t)m);
                    memcpy(nv, ev, sizeof(int) * (size_t)m);
                    free(best_u);
                    free(best_v);
                    best_u = nu;
                    best_v = nv;
                    best_n = n;
                    best_m = m;
                }
            }
        }
    }

    if (best_n == 0) {
        /* No baseline and no lift: K_{d,d} has diameter 2. */
        int d = d_ > 0 ? d_ : 1;
        best_n = 2 * d;
        best_m = d * d;
        best_u = malloc(sizeof(int) * (size_t)best_m);
        best_v = malloc(sizeof(int) * (size_t)best_m);
        int idx = 0;
        for (i = 0; i < d; i++)
            for (j = 0; j < d; j++) {
                best_u[idx] = i;
                best_v[idx] = d + j;
                idx++;
            }
    }
    printf("%d %d\n", best_n, best_m);
    for (i = 0; i < best_m; i++) printf("%d %d\n", best_u[i], best_v[i]);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q <= 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = (n, [(i, (i + 1) % n) for i in range(n)])
        if lib.is_valid(cyc[0], cyc[1], d, D):
            return cyc
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound, or degree too large for the C engine.
    if best_n >= lib.moore_bound(d, D) or d > 80:
        return best

    elapsed = time.monotonic() - t0
    if time_limit >= 10:
        budget = 0.8 * time_limit - 3.0 - elapsed
    else:
        budget = 0.4 * time_limit - elapsed
    if budget < 0.5:
        return best

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
    except (RuntimeError, ValueError, OSError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

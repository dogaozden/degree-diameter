"""Bi-Cayley (multi-base voltage) lift search for the bipartite degree-diameter problem.

Parent approach: a single Haar graph Cay(G, S) on one group, which stalls near the record.
This version uses a different family: a base of B left classes and B right classes
(B = 1, 2 or 3). Left class i has d darts (slots), and slot k = i*d + t goes to right class
tgt = (t + i) % B with group element s_k. The graph has vertices L_{i,g} and R_{j,h}, and
edges L_{i,g} -- R_{j, g*s_k}. It is bipartite, simple and d-regular. Left translations are
automorphisms, so the diameter is decided by 2B BFS runs, one from each class identity.

Search: simulated annealing over the slot elements, on cyclic groups and on F_p x| H_c
(p prime). Candidates run in ascending order of vertex count, and the search keeps going
above the best order found. Phase A (B = 1) gives a fallback. Phase B (B = 2, 3) aims above it.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search over small groups.
 * Usage: prog d D seed time_limit lo hi mask
 *   lo, hi: range of total vertex counts; bit (b-1) of mask enables base size b (b = 1..3).
 * Vertices: left class i, element g -> i*N+g; right class j, element h -> B*N + j*N + h.
 * Slot k = i*d+t has target class (t+i)%B and group element sel[k]; edge L_{i,g} -- R_{tgt, g*sel}.
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 4700
#define MAXV 30000
#define MAXS 96
#define MAXD 32
#define MAXCAND 60000

typedef struct { int type, N, q, c, B; } Cand;  /* type 0: cyclic Z_N; type 1: F_q x| H_c */

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static int prime_factors(int m, int *fs) {
    int n = 0;
    for (int f = 2; f * f <= m; f++)
        if (m % f == 0) {
            fs[n++] = f;
            while (m % f == 0) m /= f;
        }
    if (m > 1) fs[n++] = m;
    return n;
}
static int is_prime_i(int n) {
    if (n < 2) return 0;
    for (int f = 2; f * f <= n; f++)
        if (n % f == 0) return 0;
    return 1;
}

/* ------------------------------------------------------------ groups */

static int gtype, GN, gq, gc;
static int Hv[MAXG];

static void setup_group(const Cand *cd) {
    gtype = cd->type;
    GN = cd->N;
    gq = cd->q;
    gc = cd->c;
    if (gtype != 1) return;
    int fs[16];
    int nf = prime_factors(gq - 1, fs);
    int g = 2;
    for (; g < gq; g++) {
        int ok = 1;
        for (int i = 0; i < nf && ok; i++)
            if (powmod(g, (gq - 1) / fs[i], gq) == 1) ok = 0;
        if (ok) break;
    }
    long h = powmod(g, (gq - 1) / gc, gq);
    Hv[0] = 1;
    for (int j = 1; j < gc; j++) Hv[j] = (int)((long)Hv[j - 1] * h % gq);
}

/* Element (a, j) coded as a*c + j; (a,j)(b,t) = (a + H_j*b, j+t). */
static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int r = x + y;
        if (r >= GN) r -= GN;
        return r;
    }
    int a = x / gc, j = x - a * gc;
    int b = y / gc, t = y - b * gc;
    int na = (int)(((long)Hv[j] * b + a) % gq);
    int nj = j + t;
    if (nj >= gc) nj -= gc;
    return na * gc + nj;
}

static inline int ginv(int x) {
    if (gtype == 0) return x ? GN - x : 0;
    int a = x / gc, j = x - a * gc;
    int nj = (gc - j) % gc;
    int nb = (int)((long)((gq - a) % gq) * Hv[nj] % gq);
    return nb * gc + nj;
}

/* ------------------------------------------------------------ bi-Cayley state */

static int B, nslot;
static int tgt[MAXS];
static int Sel[MAXS];
static int fwd[MAXS][MAXG], bwd[MAXS][MAXG];
static int slotsR[3][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void assign_targets(void) {
    int cnt[3] = {0, 0, 0};
    for (int k = 0; k < nslot; k++) {
        int i = k / d, t = k % d;
        tgt[k] = (t + i) % B;
        slotsR[tgt[k]][cnt[tgt[k]]++] = k;
    }
}

static void setrow(int k) {
    int s = Sel[k], si = ginv(s);
    for (int g = 0; g < GN; g++) {
        fwd[k][g] = gmul(g, s);
        bwd[k][g] = gmul(g, si);
    }
}

/* True if element s is already used by another slot in the same (left class, target) group. */
static int conflict(int k, int s) {
    int i = k / d, j = tgt[k];
    for (int k2 = i * d; k2 < i * d + d; k2++)
        if (k2 != k && tgt[k2] == j && Sel[k2] == s) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int k = i * d + t;
                    int u = BN + tgt[k] * N + fwd[k][g];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int w = v - BN, j = w / N, h = w - j * N;
                for (int t = 0; t < d; t++) {
                    int k = slotsR[j][t];
                    int u = (k / d) * N + bwd[k][h];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs, using one representative per class (left translations are automorphisms). */
static long cost_all(void) {
    long V = 2L * B * GN, c = 0;
    for (int s = 0; s < 2 * B; s++) c += V - bfs_count(s * GN);
    return c;
}

/* Simulated annealing on the slot elements of the current group and base.
 * Returns 1 when diameter <= D is reached, 0 on timeout. */
static int search_candidate(double until) {
    const int iters = 40000;
    while (now() < until) {
        for (int k = 0; k < nslot; k++) Sel[k] = -1;
        for (int k = 0; k < nslot; k++) {
            int s;
            do s = rndint(GN); while (conflict(k, s));
            Sel[k] = s;
        }
        for (int k = 0; k < nslot; k++) setrow(k);
        long cost = cost_all();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if (now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(nslot);
            int s;
            do s = rndint(GN); while (s == Sel[k] || conflict(k, s));
            int old = Sel[k];
            Sel[k] = s;
            setrow(k);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                Sel[k] = old;
                setrow(k);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    long tx = 2L * x->B * x->N, ty = 2L * y->B * y->N;
    if (tx != ty) return tx < ty ? -1 : 1;
    if (x->type != y->type) return x->type - y->type;
    return x->B - y->B;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    int mask = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    int nc = 0;
    for (int b = 1; b <= 3; b++) {
        if (!(mask & (1 << (b - 1)))) continue;
        long Nlo = (lo + 2L * b - 1) / (2L * b), Nhi = hi / (2L * b);
        if (Nhi > MAXG) Nhi = MAXG;
        if (Nlo < d + 2) Nlo = d + 2;
        for (long N = Nlo; N <= Nhi && nc < MAXCAND; N++) {
            Cand cd = {0, (int)N, 0, 0, b};
            cand[nc++] = cd;
        }
        for (int q = 3; q <= MAXG; q++) {
            if (!is_prime_i(q)) continue;
            for (int c = 2; c < q && (long)q * c <= Nhi; c++) {
                if ((q - 1) % c) continue;
                long N = (long)q * c;
                if (N < Nlo) continue;
                if (nc < MAXCAND) {
                    Cand cd = {1, (int)N, q, c, b};
                    cand[nc++] = cd;
                }
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending passes. A success raises the bar; later candidates must be larger. */
    long bestT = lo - 1;
    int found = 0;
    Cand bestC;
    int bestSel[MAXS];
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            long T = 2L * cand[ci].B * cand[ci].N;
            if (T <= bestT) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_group(&cand[ci]);
            B = cand[ci].B;
            nslot = B * d;
            assign_targets();
            if (search_candidate(now() + slice)) {
                bestT = T;
                bestC = cand[ci];
                found = 1;
                for (int k = 0; k < nslot; k++) bestSel[k] = Sel[k];
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    setup_group(&bestC);
    B = bestC.B;
    nslot = B * d;
    assign_targets();
    for (int k = 0; k < nslot; k++) {
        Sel[k] = bestSel[k];
        setrow(k);
    }
    int N = GN, BN = B * N;
    printf("%d %d\n", 2 * BN, BN * d);
    for (int i = 0; i < B; i++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < d; t++) {
                int k = i * d + t;
                printf("%d %d\n", i * N + g, BN + tgt[k] * N + fwd[k][g]);
            }
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _search(d, D, seed, budget, lo, hi, mask):
    """Run the C bi-Cayley search; returns (n, edges), or (0, []) if it found nothing."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, mask],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if D >= 3 and d >= 2:
        mb = lib.moore_bound(d, D)
        avail = 0.85 * time_limit - (time.monotonic() - t0) - 4.0
        if avail > 3.0:
            # Phase A: single-base lifts (B = 1), a fallback that climbs as far as it can.
            lo_a = max(best[0] + 1, mb // 8)
            hi_a = mb // 3
            if lo_a <= hi_a:
                try:
                    consider(_search(d, D, seed, 0.3 * avail, lo_a, hi_a, 1))
                except Exception:
                    pass
            # Phase B: bi-Cayley lifts with 2 or 3 base classes, aimed above the current best.
            left = 0.85 * time_limit - (time.monotonic() - t0) - 4.0
            lo_b = best[0] + 1
            if left > 3.0 and lo_b <= mb:
                try:
                    consider(_search(d, D, seed + 1, left, lo_b, mb, 6))
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

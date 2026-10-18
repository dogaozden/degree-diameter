"""Bi-Cayley lift search over Z_m x| Z_k2, with the annealer moved into C.

Changes from the parent:
- The whole annealing loop (reach bitmasks, duplicate-dart penalty, layer swaps,
  defect-targeted voltage moves) runs in C. Python only picks k and the group
  and runs short C slices, so each C slice does thousands of times more moves.
- New move in C: a "greedy kick". It samples up to 24 voltages for one dart and
  keeps the best one if it does not worsen the cost (plateau moves allowed).
- The W(q) quadrangle is used only for D == 4, since it is too small to be useful at D = 5.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000L
#define ITERS 20000L
#define PATIENCE 4000L

typedef struct {
    int d, D, k, m, k2, r, G, N;
    int *pw;
    int *nbr;   /* nbr[l*N + v]: neighbour of v in layer l */
    int *lay;   /* lay[l*k + i]: B block of A block i in layer l */
    int *sv;    /* sv[l*k + i]: voltage of that dart */
    uint32_t *acc, *cand, *sc1, *sc2;
    uint64_t rng;
    double t_end;
    unsigned char pc[256];
} St;

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rng_next(St *s) {
    uint64_t x = s->rng;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    s->rng = x;
    return x * 2685821657736338717ULL;
}
static int rnd(St *s, int n) { return (int)((rng_next(s) >> 11) % (uint64_t)n); }
static double rndf(St *s) { return (double)(rng_next(s) >> 11) * (1.0 / 9007199254740992.0); }

/* Semidirect product Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(const St *s, int x, int y) {
    int a = x / s->k2, b = x % s->k2;
    int c = y / s->k2, e = y % s->k2;
    long long t = ((long long)s->pw[b] * c) % s->m;
    int aa = (int)((a + t) % s->m);
    return aa * s->k2 + (b + e) % s->k2;
}

static int ginv(const St *s, int x) {
    int a = x / s->k2, b = x % s->k2;
    int nb = (s->k2 - b) % s->k2;
    long long t = ((long long)s->pw[nb] * a) % s->m;
    int na = (int)((s->m - t) % s->m);
    return na * s->k2 + nb;
}

/* A block i (index i) joins B block j (index k+j) with voltage v:
   A_{i,g} ~ B_{j, g*v}, equivalently B_{j,h} ~ A_{i, h*v^-1}. */
static void set_dart(St *s, int l, int i, int j, int v) {
    int G = s->G, N = s->N, k = s->k;
    int vi = ginv(s, v);
    int *nb = s->nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        nb[i * G + g] = (k + j) * G + gmul(s, g, v);
        nb[(k + j) * G + g] = i * G + gmul(s, g, vi);
    }
}

static long dupcount(const St *s) {
    int n = s->d * s->k, k = s->k;
    long dup = 0;
    for (int p = 0; p < n; p++)
        for (int q = 0; q < p; q++)
            if (p % k == q % k && s->lay[p] == s->lay[q] && s->sv[p] == s->sv[q])
                dup++;
    return dup;
}

/* Computes cost into s->cand. Cost = unreached (rep block, vertex) pairs + PEN * duplicate darts. */
static long eval_cost(St *s) {
    int k = s->k, N = s->N, d = s->d, D = s->D;
    uint32_t *cur = s->sc1, *nxt = s->sc2;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * s->G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = cur[v];
            for (int l = 0; l < d; l++) r |= cur[s->nbr[(size_t)l * N + v]];
            nxt[v] = r;
            if (r != cur[v]) changed = 1;
        }
        uint32_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    memcpy(s->cand, cur, sizeof(uint32_t) * (size_t)N);
    long bits = 0;
    for (int v = 0; v < N; v++) bits += s->pc[s->cand[v] & 255u];
    long unreached = 2L * k * N - bits;
    return unreached + PEN * dupcount(s);
}

static void swap_buf(St *s) {
    uint32_t *t = s->acc;
    s->acc = s->cand;
    s->cand = t;
}

static void random_init(St *s) {
    int k = s->k, d = s->d;
    int perm[8];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd(s, i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) s->lay[l * k + i] = perm[i];
    }
    for (int p = 0; p < d * k; p++) s->sv[p] = rnd(s, s->G);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            set_dart(s, l, i, s->lay[l * k + i], s->sv[l * k + i]);
}

/* One annealing run from a random start. Returns 1 if cost 0 reached, 0 if not, -1 on timeout.
   On return the nbr table and acc buffer describe the current accepted state. */
static int anneal(St *s) {
    int k = s->k, d = s->d, G = s->G, N = s->N;
    uint32_t full = (1u << (2 * k)) - 1u;
    random_init(s);
    long cost = eval_cost(s);
    swap_buf(s);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost;
    long last = 0;

    for (long t = 0; t < ITERS; t++) {
        if (cost == 0) break;
        if ((t & 7) == 0 && now_s() > s->t_end) return -1;
        if (t - last > PATIENCE) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;
        double x = rndf(s);

        if (k >= 2 && x < 0.25) {
            /* Layer swap: exchange the B targets of two A blocks in one layer. */
            int l = rnd(s, d);
            int i1 = rnd(s, k), i2 = rnd(s, k - 1);
            if (i2 >= i1) i2++;
            int *lay = s->lay + (size_t)l * k;
            int *sv = s->sv + (size_t)l * k;
            int tt = lay[i1]; lay[i1] = lay[i2]; lay[i2] = tt;
            set_dart(s, l, i1, lay[i1], sv[i1]);
            set_dart(s, l, i2, lay[i2], sv[i2]);
            long c2 = eval_cost(s);
            if (c2 <= cost || rndf(s) < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                swap_buf(s);
                if (cost < best) { best = cost; last = t; }
            } else {
                tt = lay[i1]; lay[i1] = lay[i2]; lay[i2] = tt;
                set_dart(s, l, i1, lay[i1], sv[i1]);
                set_dart(s, l, i2, lay[i2], sv[i2]);
            }
        } else if (x < 0.33) {
            /* Greedy kick: try up to 24 voltages for one dart, keep the best if it does not worsen. */
            int l = rnd(s, d), i = rnd(s, k);
            int p = l * k + i;
            int old = s->sv[p];
            int tries = G < 24 ? G : 24;
            int bestv = old;
            long bestc = -1;
            for (int q = 0; q < tries; q++) {
                int nv = (G <= 24) ? q : rnd(s, G);
                if (nv == old) continue;
                set_dart(s, l, i, s->lay[p], nv);
                long c2 = eval_cost(s);
                if (bestc < 0 || c2 < bestc) { bestc = c2; bestv = nv; }
            }
            if (bestc < 0 || bestc > cost) {
                set_dart(s, l, i, s->lay[p], old);
            } else {
                s->sv[p] = bestv;
                set_dart(s, l, i, s->lay[p], bestv);
                cost = eval_cost(s);
                swap_buf(s);
                if (cost < best) { best = cost; last = t; }
            }
        } else {
            /* Voltage move, defect-targeted with probability 0.4. */
            int l, i;
            int bad = 0;
            for (int v = 0; v < N; v++) if (s->acc[v] != full) bad++;
            if (bad > 0 && rndf(s) < 0.4) {
                int target = rnd(s, bad), u = 0;
                for (int v = 0; v < N; v++) {
                    if (s->acc[v] != full) {
                        if (target == 0) { u = v; break; }
                        target--;
                    }
                }
                int block = u / G;
                l = rnd(s, d);
                if (block < k) {
                    i = block;
                } else {
                    i = 0;
                    for (int q = 0; q < k; q++)
                        if (s->lay[l * k + q] == block - k) { i = q; break; }
                }
            } else {
                l = rnd(s, d);
                i = rnd(s, k);
            }
            int p = l * k + i;
            int old = s->sv[p];
            int nv = rnd(s, G);
            if (nv == old) continue;
            s->sv[p] = nv;
            set_dart(s, l, i, s->lay[p], nv);
            long c2 = eval_cost(s);
            if (c2 <= cost || rndf(s) < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                swap_buf(s);
                if (cost < best) { best = cost; last = t; }
            } else {
                s->sv[p] = old;
                set_dart(s, l, i, s->lay[p], old);
            }
        }
    }
    return cost == 0 ? 1 : 0;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int k = atoi(argv[5]), m = atoi(argv[6]), k2 = atoi(argv[7]), r = atoi(argv[8]);
    if (d < 1 || D < 1 || k < 1 || k > 4 || m < 2 || k2 < 1 || r < 0 || r >= m) {
        printf("0 0\n"); return 0;
    }
    if (gcd_i(r, m) != 1) { printf("0 0\n"); return 0; }

    St st;
    memset(&st, 0, sizeof st);
    st.d = d; st.D = D; st.k = k; st.m = m; st.k2 = k2; st.r = r;
    st.G = m * k2;
    st.N = 2 * k * st.G;
    if ((long long)st.N > 4000000LL) { printf("0 0\n"); return 0; }
    int G = st.G, N = st.N;

    st.pw = (int *)malloc(sizeof(int) * (size_t)k2);
    st.pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) st.pw[b] = (int)(((long long)st.pw[b - 1] * r) % m);
    if ((((long long)st.pw[k2 - 1] * r) % m) != (1 % m)) { printf("0 0\n"); return 0; }

    st.nbr = (int *)malloc(sizeof(int) * (size_t)d * (size_t)N);
    st.lay = (int *)malloc(sizeof(int) * (size_t)d * (size_t)k);
    st.sv = (int *)malloc(sizeof(int) * (size_t)d * (size_t)k);
    st.acc = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)N);
    st.cand = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)N);
    st.sc1 = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)N);
    st.sc2 = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)N);
    if (!st.nbr || !st.lay || !st.sv || !st.acc || !st.cand || !st.sc1 || !st.sc2) {
        printf("0 0\n"); return 0;
    }

    for (int i = 0; i < 256; i++) st.pc[i] = (unsigned char)(i == 0 ? 0 : (st.pc[i >> 1] + (i & 1)));
    st.rng = (uint64_t)seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (st.rng == 0) st.rng = 1;
    st.t_end = now_s() + tl;

    int result = 0;
    while (now_s() < st.t_end) {
        int res = anneal(&st);
        if (res < 0) break;
        if (res == 1) { result = 1; break; }
    }

    if (!result) { printf("0 0\n"); return 0; }
    int A = k * G;
    printf("%d %d\n", N, A * d);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, st.nbr[(size_t)l * N + u]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and small constructions (Python).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group sampling and C search driver.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral type
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _c_search(d, D, seed, secs, k, m, k2, r):
    """Run one C annealing slice for a fixed group. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.3f}", k, m, k2, r],
                    stdin_graph=None, timeout=secs + 10.0)
    n, edges = lib.parse_graph_text(out)
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3 * time_limit, min(0.9 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        try:
            res = _c_search(d, D, rng.randrange(1, 1 << 30), min(remaining, 4.0),
                            k, m, k2, r)
        except Exception:
            break
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

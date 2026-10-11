import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an arbitrary explicit finite group.
#
# Groups come from three families built by formula inside C:
#   type 0: Z_m x| Z_k with action r (u,v)(u',v') = (u + r^v u', v + v')
#   type 1: Heisenberg group of order p^3
#   type 2: Z_p^2 x| Z_k with diagonal action (r1, r2)
#
# A lift has K A-orbits and K B-orbits, each of size N (the group order).
# There are DEG layers. Layer l has a permutation pi_l of {0..K-1} and
# voltages s_{l,i}. Edge: A_{i,g} -- B_{pi_l(i), g*s_{l,i}}. Left
# multiplication is an automorphism, so diameter <= D iff BFS of depth D
# from each of the 2K orbit representatives reaches every vertex.
#
# Cost = total uncovered (source, vertex) pairs + PEN * duplicate edges.
# Simulated annealing runs from random states on randomly chosen
# (group, K) pairs whose order lies in a window just above the best
# order found so far. Each valid state raises the window.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXSPEC 2048
#define MAXN 1000
#define MAXK 3
#define MAXDEG 16
#define MAXV (2 * MAXK * MAXN)
#define MAXM (MAXDEG * MAXK * MAXN)
#define ITERS 20000
#define TSTART 6.0
#define TEND 0.3
#define PEN 40

typedef struct { int type, a, b, c, d, N; } Spec;

static Spec specs[MAXSPEC];
static int nspec = 0;

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gpow_mod(int base, int e, int m) {
    long long r = 1 % m, x = base % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int parse_spec(const char *str, Spec *sp) {
    int t, a, b, c, d;
    if (sscanf(str, "%d:%d:%d:%d:%d", &t, &a, &b, &c, &d) != 5) return 0;
    sp->type = t; sp->a = a; sp->b = b; sp->c = c; sp->d = d;
    if (t == 0) sp->N = a * b;
    else if (t == 1) sp->N = a * a * a;
    else if (t == 2) sp->N = a * a * b;
    else return 0;
    return 1;
}

static int spec_valid(const Spec *s) {
    int N = s->N;
    if (N < 2 || N > MAXN) return 0;
    if (s->type == 0) {
        int m = s->a, k = s->b, r = s->c;
        if (m < 2 || k < 1) return 0;
        if (r < 1 || r >= m) return 0;
        if (gcd_i(r, m) != 1) return 0;
        return gpow_mod(r, k, m) == 1 % m;
    } else if (s->type == 1) {
        return s->a >= 2;
    } else if (s->type == 2) {
        int p = s->a, k = s->b, r1 = s->c, r2 = s->d;
        if (p < 2 || k < 1) return 0;
        if (r1 < 1 || r1 >= p || r2 < 1 || r2 >= p) return 0;
        return gpow_mod(r1, k, p) == 1 % p && gpow_mod(r2, k, p) == 1 % p;
    }
    return 0;
}

/* Current group multiplication table and current configuration. */
static int mt[MAXN * MAXN];
static int rp1[MAXN], rp2[MAXN];
static int DEG, DIAM;
static int K, N, NTOT;
static int pi_[MAXDEG][MAXK];
static int sv[MAXDEG][MAXK];
static int adj[MAXV * MAXDEG];
static int stamp[MAXV];
static int fbuf[MAXV], nbuf[MAXV];
static int gen = 0;
static int best_n = 0, best_m = 0;
static int best_e[2 * MAXM];

static void build_table(const Spec *s) {
    int G = s->N;
    if (s->type == 0) {
        int m = s->a, k = s->b, r = s->c;
        for (int v = 0; v < k; v++) rp1[v] = gpow_mod(r, v, m);
        for (int x = 0; x < G; x++) {
            int u = x / k, v = x % k;
            for (int y = 0; y < G; y++) {
                int u2 = y / k, v2 = y % k;
                int U = (int)(((long long)u + (long long)rp1[v] * u2) % m);
                int V = (v + v2) % k;
                mt[x * G + y] = U * k + V;
            }
        }
    } else if (s->type == 1) {
        int p = s->a, pp = p * p;
        for (int x = 0; x < G; x++) {
            int a = x / pp, b = (x / p) % p, c = x % p;
            for (int y = 0; y < G; y++) {
                int a2 = y / pp, b2 = (y / p) % p, c2 = y % p;
                int A = (a + a2) % p;
                int B = (b + b2) % p;
                int C = (c + c2 + a * b2) % p;
                mt[x * G + y] = (A * p + B) * p + C;
            }
        }
    } else {
        int p = s->a, k = s->b, r1 = s->c, r2 = s->d;
        for (int v = 0; v < k; v++) {
            rp1[v] = gpow_mod(r1, v, p);
            rp2[v] = gpow_mod(r2, v, p);
        }
        for (int x = 0; x < G; x++) {
            int v = x % k, t = x / k, w = t % p, u = t / p;
            for (int y = 0; y < G; y++) {
                int v2 = y % k, t2 = y / k, w2 = t2 % p, u2 = t2 / p;
                int U = (int)(((long long)u + (long long)rp1[v] * u2) % p);
                int W = (int)(((long long)w + (long long)rp2[v] * w2) % p);
                int V = (v + v2) % k;
                mt[x * G + y] = (U * p + W) * k + V;
            }
        }
    }
}

static void random_state(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            pi_[l][i] = p[i];
            sv[l][i] = rnd_int(N);
        }
    }
}

/* Uncovered pairs over the 2K orbit representatives plus duplicate-edge penalty. */
static long long eval_cost(void) {
    const int n = NTOT;
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int j = pi_[l][i], s = sv[l][i];
            for (int g = 0; g < N; g++) {
                int a = i * N + g;
                int b = (K + j) * N + mt[g * N + s];
                adj[a * DEG + l] = b;
                adj[b * DEG + l] = a;
            }
        }
    long long dup = 0;
    for (int a = 0; a < K * N; a++) {
        const int *au = adj + a * DEG;
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (au[l] == au[l2]) dup++;
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * N;
        gen++;
        if (gen >= 2000000000) {
            memset(stamp, 0, sizeof(stamp));
            gen = 1;
        }
        int *f = fbuf, *h = nbuf;
        int fs = 1, reached = 1;
        f[0] = src;
        stamp[src] = gen;
        for (int lv = 0; lv < DIAM && fs > 0; lv++) {
            int ns = 0;
            for (int q = 0; q < fs; q++) {
                const int *au = adj + f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != gen) {
                        stamp[v] = gen;
                        h[ns++] = v;
                    }
                }
            }
            reached += ns;
            int *tmp = f; f = h; h = tmp;
            fs = ns;
        }
        total += n - reached;
    }
    return total + dup * PEN;
}

static int mv_kind, mv_l, mv_i, mv_i2, mv_old;

static void do_move(void) {
    mv_kind = 0;
    if (K > 1 && rnd_unit() < 0.3) {
        mv_l = rnd_int(DEG);
        mv_i = rnd_int(K);
        mv_i2 = rnd_int(K);
        if (mv_i != mv_i2) {
            mv_kind = 1;
            int t = pi_[mv_l][mv_i];
            pi_[mv_l][mv_i] = pi_[mv_l][mv_i2];
            pi_[mv_l][mv_i2] = t;
        }
    } else {
        mv_kind = 2;
        mv_l = rnd_int(DEG);
        mv_i = rnd_int(K);
        mv_old = sv[mv_l][mv_i];
        sv[mv_l][mv_i] = rnd_int(N);
    }
}

static void undo_move(void) {
    if (mv_kind == 1) {
        int t = pi_[mv_l][mv_i];
        pi_[mv_l][mv_i] = pi_[mv_l][mv_i2];
        pi_[mv_l][mv_i2] = t;
    } else if (mv_kind == 2) {
        sv[mv_l][mv_i] = mv_old;
    }
}

static long long anneal(void) {
    long long cur = eval_cost();
    for (int it = 0; it < ITERS && cur > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double temp = TSTART * pow(TEND / TSTART, (double)it / ITERS);
        do_move();
        long long nc = eval_cost();
        long long dl = nc - cur;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / temp)) {
            cur = nc;
        } else {
            undo_move();
        }
    }
    return cur;
}

static void emit_state(void) {
    int idx = 0;
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int j = pi_[l][i], s = sv[l][i];
            for (int g = 0; g < N; g++) {
                best_e[idx++] = i * N + g;
                best_e[idx++] = (K + j) * N + mt[g * N + s];
            }
        }
    best_m = DEG * K * N;
    best_n = NTOT;
}

int main(int argc, char **argv) {
    timespec_get(&T0, TIME_UTC);
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int lo = atoi(argv[5]);
    int nspec_cnt = 0;
    for (int i = 6; i < argc && nspec < MAXSPEC; i++) {
        Spec sp;
        if (parse_spec(argv[i], &sp) && spec_valid(&sp)) {
            specs[nspec++] = sp;
        }
        nspec_cnt++;
    }
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || nspec == 0) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static int cs[MAXSPEC * MAXK];
    static int ck[MAXSPEC * MAXK];
    int thr = lo;
    while (elapsed() < DEADLINE) {
        int hi = thr + thr / 6 + 10;
        int nc = 0;
        for (int si = 0; si < nspec; si++)
            for (int k = 1; k <= MAXK; k++) {
                long long nn = 2LL * k * specs[si].N;
                if (nn >= thr && nn <= hi) {
                    cs[nc] = si;
                    ck[nc] = k;
                    nc++;
                }
            }
        if (nc == 0) break;
        int pick = rnd_int(nc);
        Spec *s = &specs[cs[pick]];
        K = ck[pick];
        N = s->N;
        NTOT = 2 * K * N;
        build_table(s);
        random_state();
        long long c = anneal();
        if (c == 0 && NTOT > best_n) {
            emit_state();
            thr = NTOT + 2;
        }
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Group candidates for the C search: Heisenberg groups, Z_p^2 x| Z_k with
# diagonal action, and metacyclic / abelian semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _group_specs(lo_n, hi_n, seed, cap=400):
    rng = random.Random(seed * 7919 + 13)
    fixed = []
    rest = []
    for p in (3, 5, 7):
        if lo_n <= p ** 3 <= hi_n:
            fixed.append((1, p, 0, 0, 0))
    for p in (3, 5, 7, 11, 13):
        for k in range(2, hi_n // (p * p) + 1):
            N = p * p * k
            if N < lo_n or N > hi_n:
                continue
            roots = [r for r in range(1, p) if pow(r, k, p) == 1 % p]
            for r1 in roots:
                for r2 in roots:
                    rest.append((2, p, k, r1, r2))
    for N in range(max(lo_n, 4), hi_n + 1):
        for k in range(2, N // 2 + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    rest.append((0, m, k, r, 0))
    if len(rest) > cap:
        rest = rng.sample(rest, cap)
    out = fixed + rest
    return [f"{t}:{a}:{b}:{c}:{e}" for (t, a, b, c, e) in out]


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C annealer over explicit groups.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    remaining = 0.80 * time_limit - (time.monotonic() - start) - 3.0
    if remaining >= 3.0 and d <= 16:
        lo = max(best_n + 1, int(0.40 * moore))
        hi = int(lo * 1.3)
        specs = _group_specs(max(2, lo // 6), hi // 2 + 1, seed)
        if specs:
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, seed, f"{remaining:.2f}", lo, *specs],
                                timeout=remaining + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

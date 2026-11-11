"""Bold variant: bi-Cayley lifts over semidirect groups, searched in C with a binary search on order.

The C engine picks a random group Z_m x| Z_k, a p-vertex base (sum of d permutations), and d*p voltages.
Validity is checked from the 2p block representatives, since the lift is invariant under left multiplication.
Exact constructions (projective planes, Araujo-Pardo-Lopez, generalized quadrangles) still run first.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: bi-Cayley lifts over Z_m x| Z_k with a p-vertex base, simulated annealing
# on the number of unreached (representative, vertex) pairs, binary search on order.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley lift search.
 * Usage: prog d D seed time_limit hi
 * Searches for a bipartite lift of order N (N <= hi, as large as found) with max degree d
 * and diameter <= D. Vertices: A_{i,x} = i*G + x, B_{j,y} = p*G + j*G + y, group G = Z_m x| Z_k.
 * Dart (i,j,g) joins A_{i,x} to B_{j, x*g}. The lift is invariant under left multiplication,
 * so checking BFS from the 2p block identities certifies the whole diameter.
 * Output: "N m" and edge lines for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 8192
#define MAXD 32
#define MAXP 4
#define MAXDARTS (MAXD * MAXP)

typedef struct { int i, j, g, gi; } Dart;

typedef struct {
    int p, G, m, k, r;
    int nd;
    Dart dt[MAXDARTS];
} Sol;

static int d, D;
static double t_end;
static Sol BEST;
static int have_best = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

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

/* Current group: element a*GK+b, (a,b)(c,e) = (a + r^b c mod GM, b+e mod GK). */
static int GM = 1, GK = 1;
static int RP[MAXV];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    RP[0] = 1 % m;
    for (int t = 1; t < k; t++) RP[t] = (int)((long)RP[t - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = ((long)a + (long)RP[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long na = ((long)GM - (long)RP[nb] * a % GM) % GM;
    return (int)(na * GK + nb);
}

static int nbrs(const Sol *s, int v, int *out) {
    int G = s->G, p = s->p, c = 0;
    if (v < p * G) {
        int i = v / G, x = v % G;
        for (int t = 0; t < s->nd; t++)
            if (s->dt[t].i == i)
                out[c++] = p * G + s->dt[t].j * G + gmul(x, s->dt[t].g);
    } else {
        int u = v - p * G, j = u / G, y = u % G;
        for (int t = 0; t < s->nd; t++)
            if (s->dt[t].j == j)
                out[c++] = s->dt[t].i * G + gmul(y, s->dt[t].gi);
    }
    return c;
}

static int vst[MAXV];
static int vstamp = 0;
static int bq[MAXV];

/* Sum over the 2p block identities of the number of vertices NOT within distance D. */
static long cost_of(const Sol *s) {
    int N = 2 * s->p * s->G;
    long unc = 0;
    for (int r = 0; r < 2 * s->p; r++) {
        int root = r < s->p ? r * s->G : s->p * s->G + (r - s->p) * s->G;
        vstamp++;
        int tail = 0;
        bq[tail++] = root;
        vst[root] = vstamp;
        int fs = 0, fe = 1;
        for (int dep = 0; dep < D && fs < fe; dep++) {
            for (int q = fs; q < fe; q++) {
                int buf[MAXD];
                int c = nbrs(s, bq[q], buf);
                for (int k = 0; k < c; k++) {
                    int u = buf[k];
                    if (vst[u] != vstamp) {
                        vst[u] = vstamp;
                        bq[tail++] = u;
                    }
                }
            }
            fs = fe;
            fe = tail;
        }
        unc += N - tail;
    }
    return unc;
}

/* Random base p x p matrix with row and column sums d, connected as a bipartite graph. */
static void random_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP], st[2 * MAXP], top = 0, ns = 1;
        memset(seen, 0, sizeof(seen));
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * p) return;
    }
}

/* Uniformly random group Z_m x| Z_k of order G (reservoir sampling over all valid (m,k,r)). */
static int pick_group(long G, int *om, int *ok, int *orr) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (long k = 1; k <= G; k++) {
        if (G % k) continue;
        long m = G / k;
        if (m == 1) {
            cnt++;
            if (rnd() % (uint64_t)cnt == 0) { bm = 1; bk = (int)k; br = 0; }
            continue;
        }
        for (long r = 1; r < m; r++) {
            if (gcdl(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rnd() % (uint64_t)cnt == 0) { bm = (int)m; bk = (int)k; br = (int)r; }
        }
    }
    if (!cnt) return 0;
    *om = bm;
    *ok = bk;
    *orr = br;
    return 1;
}

static void init_darts(Sol *s) {
    int M[MAXP][MAXP];
    random_base(s->p, M);
    s->nd = 0;
    for (int i = 0; i < s->p; i++)
        for (int j = 0; j < s->p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                int g;
                for (;;) {
                    g = rndint(s->G);
                    int clash = 0;
                    for (int t = 0; t < s->nd; t++)
                        if (s->dt[t].i == i && s->dt[t].j == j && s->dt[t].g == g) { clash = 1; break; }
                    if (!clash) break;
                }
                s->dt[s->nd].i = i;
                s->dt[s->nd].j = j;
                s->dt[s->nd].g = g;
                s->dt[s->nd].gi = ginv(g);
                s->nd++;
            }
}

/* Simulated annealing on voltages (group and base fixed). Returns the final cost. */
static long sa_run(Sol *s, long steps, double until) {
    long c = cost_of(s);
    const double T0 = 2.0, T1 = 0.05;
    for (long it = 0; it < steps && c > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)steps);
        int t = rndint(s->nd);
        int i = s->dt[t].i, j = s->dt[t].j, old = s->dt[t].g, oldgi = s->dt[t].gi;
        int g = -1;
        for (int tr = 0; tr < 30 && g < 0; tr++) {
            int cand = rndint(s->G);
            if (cand == old) continue;
            int ok = 1;
            for (int u = 0; u < s->nd; u++)
                if (u != t && s->dt[u].i == i && s->dt[u].j == j && s->dt[u].g == cand) { ok = 0; break; }
            if (ok) g = cand;
        }
        if (g < 0) continue;
        s->dt[t].g = g;
        s->dt[t].gi = ginv(g);
        long c2 = cost_of(s);
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            s->dt[t].g = old;
            s->dt[t].gi = oldgi;
        }
    }
    return c;
}

/* Try to find a valid lift with at least t vertices, restarting with random group/base. */
static int probe(long t, double until) {
    if (t > 4000) return 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : 4;
        long G = (t + 2L * p - 1) / (2L * p);
        if (G < d + 1) G = d + 1;
        int m, k, rr;
        if (!pick_group(G, &m, &k, &rr)) continue;
        Sol s;
        s.p = p;
        s.G = (int)G;
        s.m = m;
        s.k = k;
        s.r = rr;
        set_group(m, k, rr);
        init_darts(&s);
        long c = sa_run(&s, 20000, until);
        if (c == 0) {
            BEST = s;
            have_best = 1;
            return 1;
        }
    }
    return 0;
}

static void print_sol(const Sol *s) {
    set_group(s->m, s->k, s->r);
    int G = s->G, p = s->p, N = 2 * p * G;
    long m = (long)s->nd * G;
    printf("%d %ld\n", N, m);
    for (int t = 0; t < s->nd; t++)
        for (int x = 0; x < G; x++)
            printf("%d %d\n", s->dt[t].i * G + x, p * G + s->dt[t].j * G + gmul(x, s->dt[t].g));
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [hi]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long hi = argc > 5 ? atol(argv[5]) : 2200;
    if (hi > 4000) hi = 4000;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit * 0.92;

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long lo = 0;
    while (now() < t_end) {
        long t = (hi - lo > 2) ? (lo + hi) / 2 : lo + 2;
        if (t > 4000) break;
        double rem = t_end - now();
        double budget = rem * 0.5;
        if (budget > 8.0) budget = 8.0;
        if (budget < 1.0) budget = rem;
        if (probe(t, now() + budget)) {
            lo = 2L * BEST.p * BEST.G;
        } else if (hi - lo > 2) {
            hi = t;
        }
    }

    if (have_best) {
        set_group(BEST.m, BEST.k, BEST.r);
        if (cost_of(&BEST) == 0) {
            print_sol(&BEST);
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Keep (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: bi-Cayley lifts over semidirect groups, binary search on order in C.
    if D >= 2 and 2 <= d <= 30:
        hi = min(lib.moore_bound(d, D), 2200)
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0 and hi > best[0] + 2:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), hi],
                                 stdin_graph=None, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

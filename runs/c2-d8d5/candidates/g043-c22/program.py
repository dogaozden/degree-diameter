"""Bi-Cayley voltage search in C over semidirect groups Z_m x| Z_k, with the same fallbacks as before."""
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
# C engine: vertex-transitive bi-Cayley search.
# Vertices A_{i,g} = i*G + g and B_{j,h} = P + j*G + h, with P = K*G.
# Layer l joins A_{i,g} to B_{sig_l(i), g*s_{l,i}}. Left multiplication by G is an
# automorphism that is transitive on each side, so diameter <= D holds iff the
# 2K block representatives reach everything within D steps.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley voltage annealing over semidirect groups Z_m x| Z_k.
 * Usage:  prog d D seed time_limit min_n
 * stdout: "n m" + edge lines for the best valid graph with n > min_n, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXP 6
#define MAXG 4096
#define MAXNV (2 * MAXP * MAXG)
#define MAXD 32
#define PEN 500

static int d, D;
static double t_end;
static long moore;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Current group Z_gm x| Z_gk, element a*gk+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gm, gk, gr;
static int rp[MAXG];

static void set_group(int m, int k2, int r) {
    gm = m; gk = k2; gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

static int pick_group(int Gs, int *pm, int *pk, int *pr) {
    long cnt = 0;
    for (int m = 1; m <= Gs; m++) {
        if (Gs % m) continue;
        int k2 = Gs / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { *pm = 1; *pk = k2; *pr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { *pm = m; *pk = k2; *pr = r; }
        }
    }
    return cnt > 0;
}

/* Current configuration. */
static int K, G, P, NV, dd;
static int sig[MAXD][MAXP], sv[MAXD][MAXP];
static int nbr[MAXNV * MAXD];
static int vis[MAXNV];
static int vstamp;
static int qbuf[MAXNV];

/* Best configuration found so far. */
static int have_best = 0;
static int best_n;
static int bK, bG, bgm, bgk, bgr;
static int bsig[MAXD][MAXP], bsv[MAXD][MAXP];

static void set_layer(int l, int i) {
    int j = sig[l][i], s = sv[l][i];
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        int a = i * G + g;
        int b = P + j * G + h;
        nbr[a * dd + l] = b;
        nbr[b * dd + l] = a;
    }
}

static int bfs_count(int src) {
    vstamp++;
    if (vstamp == 0x7fffffff) {
        memset(vis, 0, sizeof(vis));
        vstamp = 1;
    }
    int head = 0, tail = 0;
    vis[src] = vstamp;
    qbuf[tail++] = src;
    for (int depth = 0; depth < D; depth++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = qbuf[head++];
            const int *nb = nbr + (size_t)v * dd;
            for (int l = 0; l < dd; l++) {
                int u = nb[l];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    qbuf[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < dd; l++)
            for (int l2 = l + 1; l2 < dd; l2++)
                if (sig[l][i] == sig[l2][i] && sv[l][i] == sv[l2][i]) c++;
    return c;
}

static long eval_cost(void) {
    long c = 0;
    for (int b = 0; b < 2 * K; b++) c += NV - bfs_count(b * G);
    c += (long)PEN * dup_count();
    return c;
}

static void random_config(void) {
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < K; i++) sig[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[l][i];
            sig[l][i] = sig[l][j];
            sig[l][j] = t;
        }
    }
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < K; i++) {
            sv[l][i] = rndint(G);
            set_layer(l, i);
        }
}

static int anneal(double until) {
    random_config();
    long cost = eval_cost();
    double start = now();
    double span = until - start;
    if (span <= 0) return 0;
    double T = 2.0;
    for (long it = 0; ; it++) {
        if (cost == 0) return 1;
        if ((it & 127) == 0) {
            double tn = now();
            if (tn >= until) return 0;
            double frac = (tn - start) / span;
            T = 1.5 * (1.0 - frac) + 0.05;
        }
        int l = rndint(dd);
        if (K >= 2 && rnd01() < 0.3) {
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = sig[l][i1];
            sig[l][i1] = sig[l][i2];
            sig[l][i2] = t;
            set_layer(l, i1);
            set_layer(l, i2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = sig[l][i1];
                sig[l][i1] = sig[l][i2];
                sig[l][i2] = t;
                set_layer(l, i1);
                set_layer(l, i2);
            }
        } else {
            int i = rndint(K);
            int old = sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            set_layer(l, i);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                sv[l][i] = old;
                set_layer(l, i);
            }
        }
    }
}

static int full_verify(void) {
    if (dup_count()) return 0;
    for (int v = 0; v < NV; v++)
        if (bfs_count(v) != NV) return 0;
    return 1;
}

static void store_best(void) {
    have_best = 1;
    best_n = NV;
    bK = K; bG = G; bgm = gm; bgk = gk; bgr = gr;
    memcpy(bsig, sig, sizeof(sig));
    memcpy(bsv, sv, sizeof(sv));
}

static void print_best(void) {
    if (!have_best) {
        printf("0 0\n");
        return;
    }
    K = bK; G = bG; P = K * G; NV = 2 * P; dd = d;
    set_group(bgm, bgk, bgr);
    memcpy(sig, bsig, sizeof(sig));
    memcpy(sv, bsv, sizeof(sv));
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < K; i++) set_layer(l, i);
    long m = (long)P * dd;
    printf("%d %ld\n", NV, m);
    for (int v = 0; v < P; v++)
        for (int l = 0; l < dd; l++)
            printf("%d %d\n", v, nbr[v * dd + l]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_n = argc >= 6 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = moore_bound();
    dd = d;
    best_n = (int)min_n;
    have_best = 0;
    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    static const int kchoice[] = {1, 2, 2, 3, 3, 4, 4, 5, 6};
    int nk = (int)(sizeof(kchoice) / sizeof(kchoice[0]));

    while (now() < t_end) {
        K = kchoice[rndint(nk)];
        long Gmin = best_n / (2L * K) + 1;
        if (2L * K * Gmin > moore || 2L * K * Gmin > MAXNV || Gmin > MAXG) {
            K = 1;
            Gmin = best_n / 2 + 1;
            if (2L * Gmin > moore || 2L * Gmin > MAXNV || Gmin > MAXG) break;
        }
        long Gl = Gmin + rndint(3);
        if (2L * K * Gl > moore || 2L * K * Gl > MAXNV || Gl > MAXG) Gl = Gmin;
        G = (int)Gl;
        P = K * G;
        NV = 2 * P;

        int m, k2, r;
        if (!pick_group(G, &m, &k2, &r)) continue;
        set_group(m, k2, r);

        double until = now() + 4.0;
        if (until > t_end) until = t_end;
        if (anneal(until)) {
            if (NV > best_n && full_verify()) store_best();
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 3.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if (n, e) is a larger valid graph."""
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

    # Main search: C bi-Cayley annealing over semidirect groups, seeded with the best order.
    if D >= 2:
        budget = end - time.monotonic() - 1.0
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                                 stdin_graph=None, timeout=budget + 6)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

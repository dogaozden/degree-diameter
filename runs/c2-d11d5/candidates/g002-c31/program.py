"""Bi-Cayley lift search with a C annealer.

The C engine searches bi-lifts over two families of finite groups: semidirect products Z_m x| Z_k
and the affine group AGL(1,p). Every layer is a perfect matching between base vertices, so each
vertex has degree d exactly. Because left translation is an automorphism, reachability only has
to be tracked from the 2k block representatives, which keeps each evaluation cheap. Python builds
the exact constructions (PG(2,q), W(q)), passes the best order found so far to C, and validates
whatever C returns.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000L
#define NPRIMES 20

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint8_t PC[1 << 16];
static void init_pc(void) {
    PC[0] = 0;
    for (int x = 1; x < (1 << 16); x++) PC[x] = (uint8_t)(PC[x >> 1] + (x & 1));
}

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long long pw_mod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m; if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int imod(long long a, long long m) {
    long long r = a % m;
    if (r < 0) r += m;
    return (int)r;
}

/* ---------------- group ---------------- */
static int gtype = 0, gm = 1, gk2 = 1, gr = 1, gp = 3, G = 1;
static int gpow[64];
static int *ginv_tab = NULL;
static int ginv_cap = 0;

static int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
        int aa = imod((long long)a + (long long)gpow[b] * c, gm);
        return aa * gk2 + (b + e) % gk2;
    } else {
        int p = gp;
        int a = x / p + 1, b = x % p, c = y / p + 1, e = y % p;
        int A = (a * c) % p;
        int B = (a * e + b) % p;
        return (A - 1) * p + B;
    }
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / gk2, b = x % gk2;
        int nb = (gk2 - b) % gk2;
        int aa = imod(-(long long)gpow[nb] * a, gm);
        return aa * gk2 + nb;
    } else {
        int p = gp;
        int a = x / p + 1, b = x % p;
        int ai = (int)pw_mod(a, p - 2, p);
        int y = imod(-(long long)b * ai, p);
        return (ai - 1) * p + y;
    }
}

static void set_group(int type, int m, int k2, int r, int p) {
    gtype = type; gm = m; gk2 = k2; gr = r; gp = p;
    if (type == 0) {
        G = m * k2;
        gpow[0] = 1 % m;
        for (int t = 1; t < k2; t++) gpow[t] = (int)((long long)gpow[t - 1] * r % m);
    } else {
        G = (p - 1) * p;
    }
    if (G > ginv_cap) {
        free(ginv_tab);
        ginv_tab = malloc(sizeof(int) * (size_t)G);
        ginv_cap = G;
    }
    for (int x = 0; x < G; x++) ginv_tab[x] = ginv(x);
}

static int sample_semidirect(int target, int *mo, int *k2o, int *ro) {
    static const int k2s[20] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = k2s[rndi(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndu() < 0.3) {
            r = m - 1;
            if (gcd_i(r, m) != 1 || (long long)r * r % m != 1 % m) continue;
        } else {
            r = -1;
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    int c = 2 + rndi(m - 2);
                    if (gcd_i(c, m) == 1 && pw_mod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
            if (r < 0) continue;
        }
        *mo = m; *k2o = k2; *ro = r;
        return 1;
    }
    return 0;
}

/* ---------------- lift state ---------------- */
static int DEG = 11, DIAM = 5, KB = 1, N = 2;
static int *lay = NULL, *sv = NULL, *nbr = NULL;
static size_t cap_ls = 0, cap_nbr = 0;
static uint32_t *reach = NULL, *tmpr = NULL, *saved = NULL;
static size_t cap_r = 0;

static void prepare(void) {
    size_t nl = (size_t)DEG * KB;
    if (nl > cap_ls) {
        free(lay); free(sv);
        lay = malloc(nl * sizeof(int));
        sv = malloc(nl * sizeof(int));
        cap_ls = nl;
    }
    size_t nn = (size_t)DEG * N;
    if (nn > cap_nbr) {
        free(nbr);
        nbr = malloc(nn * sizeof(int));
        cap_nbr = nn;
    }
    if ((size_t)N > cap_r) {
        free(reach); free(tmpr); free(saved);
        reach = malloc((size_t)N * sizeof(uint32_t));
        tmpr = malloc((size_t)N * sizeof(uint32_t));
        saved = malloc((size_t)N * sizeof(uint32_t));
        cap_r = N;
    }
}

/* Dart (l, i): A block i joined to B block lay[l][i] with voltage sv[l][i]. */
static void set_dart(int l, int i) {
    int j = lay[(size_t)l * KB + i];
    int s = sv[(size_t)l * KB + i];
    int si = ginv_tab[s];
    int *nb = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        nb[i * G + g] = (KB + j) * G + h;
        nb[(KB + j) * G + h] = i * G + gmul(h, si);
    }
}

/* reach[v] bit b set when representative of block b is within DIAM of v. */
static void compute_reach(void) {
    for (int v = 0; v < N; v++) reach[v] = 0;
    for (int b = 0; b < 2 * KB; b++) reach[(size_t)b * G] |= (uint32_t)1 << b;
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = reach[v];
            for (int l = 0; l < DEG; l++) r |= reach[nbr[(size_t)l * N + v]];
            tmpr[v] = r;
            if (r != reach[v]) changed = 1;
        }
        memcpy(reach, tmpr, (size_t)N * sizeof(uint32_t));
        if (!changed) break;
    }
}

static long dupcount(void) {
    long dup = 0;
    int n = DEG * KB;
    for (int a = 0; a < n; a++)
        for (int b = a + 1; b < n; b++)
            if (a % KB == b % KB && lay[a] == lay[b] && sv[a] == sv[b]) dup++;
    return dup;
}

static long cost_now(void) {
    long unr = 0;
    int full = 2 * KB;
    for (int v = 0; v < N; v++) unr += full - PC[reach[v] & 0xFFFF];
    return unr + PEN * dupcount();
}

static long anneal(long iters, long patience, double deadline) {
    int full = (1 << (2 * KB)) - 1;
    for (int l = 0; l < DEG; l++) {
        int *L = lay + (size_t)l * KB;
        int *S = sv + (size_t)l * KB;
        for (int i = 0; i < KB; i++) L[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = L[i]; L[i] = L[j]; L[j] = t;
        }
        for (int i = 0; i < KB; i++) S[i] = rndi(G);
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < KB; i++) set_dart(l, i);
    compute_reach();
    long cost = cost_now();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long bestc = cost, last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if (t - last > patience) break;
        if ((t & 31) == 0 && wall() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        double x = rndu();

        if (KB >= 2 && x < 0.25) {
            int l = rndi(DEG);
            int i1 = rndi(KB), i2 = rndi(KB - 1);
            if (i2 >= i1) i2++;
            int *L = lay + (size_t)l * KB;
            int tmp = L[i1]; L[i1] = L[i2]; L[i2] = tmp;
            memcpy(saved, reach, (size_t)N * sizeof(uint32_t));
            set_dart(l, i1); set_dart(l, i2);
            compute_reach();
            long c2 = cost_now();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tmp = L[i1]; L[i1] = L[i2]; L[i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
                memcpy(reach, saved, (size_t)N * sizeof(uint32_t));
            }
            continue;
        }

        int v = -1;
        for (int tr = 0; tr < 20; tr++) {
            int u = rndi(N);
            if (reach[u] != (uint32_t)full) { v = u; break; }
        }
        int l, i;
        if (v >= 0 && rndu() < 0.4) {
            int block = v / G;
            l = rndi(DEG);
            if (block < KB) {
                i = block;
            } else {
                int j = block - KB;
                i = 0;
                for (int q = 0; q < KB; q++)
                    if (lay[(size_t)l * KB + q] == j) { i = q; break; }
            }
        } else {
            l = rndi(DEG);
            i = rndi(KB);
        }
        int *S = sv + (size_t)l * KB + i;
        int old = *S;
        int nw = rndi(G);
        if (nw == old) continue;
        memcpy(saved, reach, (size_t)N * sizeof(uint32_t));
        *S = nw;
        set_dart(l, i);
        compute_reach();
        long c2 = cost_now();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            *S = old;
            set_dart(l, i);
            memcpy(reach, saved, (size_t)N * sizeof(uint32_t));
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long seed = atol(argv[3]);
    double tl = atof(argv[4]);
    long bestN = atol(argv[5]);
    if (DEG < 2 || DIAM < 2) { printf("0 0\n"); return 0; }
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    init_pc();
    double deadline = wall() + tl;

    static const int PR[NPRIMES] = {3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73};

    int have = 0;
    int bK = 0, bType = 0, bm = 1, bk2 = 1, br = 1, bp = 3;
    int *blay = NULL, *bsv = NULL;
    double trials[7] = {0, 0, 0, 0, 0, 0, 0};
    double wins[7] = {0, 0, 0, 0, 0, 0, 0};

    while (wall() < deadline) {
        int k;
        if (rndu() < 0.2) {
            k = 1 + rndi(6);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= 6; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rndu();
                if (sc > bs) { bs = sc; k = kk; }
            }
        }
        long base = bestN / (2 * k);
        int span = (int)(base / 8 + 2);
        long target = base + 1 + rndi(span);
        if (target < 2) target = 2;

        int type, m = 1, k2 = 1, r = 1, p = 3;
        if (rndu() < 0.5) {
            int cand[NPRIMES];
            int nc = 0;
            for (int q = 0; q < NPRIMES; q++) {
                long long o = (long long)PR[q] * (PR[q] - 1);
                if (o >= target && o <= 3 * target + 50) cand[nc++] = PR[q];
            }
            if (nc == 0) continue;
            type = 1;
            p = cand[rndi(nc)];
        } else {
            if (!sample_semidirect((int)target, &m, &k2, &r)) continue;
            type = 0;
        }
        set_group(type, m, k2, r, p);
        if (2L * k * G <= bestN) continue;

        KB = k;
        N = 2 * KB * G;
        prepare();
        trials[k] += 1.0;
        if (anneal(4000, 1200, deadline)) {
            wins[k] += 1.0;
            bestN = N;
            have = 1;
            bK = k; bType = type; bm = m; bk2 = k2; br = r; bp = p;
            free(blay); free(bsv);
            blay = malloc(sizeof(int) * (size_t)DEG * KB);
            bsv = malloc(sizeof(int) * (size_t)DEG * KB);
            memcpy(blay, lay, sizeof(int) * (size_t)DEG * KB);
            memcpy(bsv, sv, sizeof(int) * (size_t)DEG * KB);
        }
    }

    if (!have) { printf("0 0\n"); return 0; }

    set_group(bType, bm, bk2, br, bp);
    KB = bK;
    N = 2 * KB * G;
    prepare();
    memcpy(lay, blay, sizeof(int) * (size_t)DEG * KB);
    memcpy(sv, bsv, sizeof(int) * (size_t)DEG * KB);
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < KB; i++) set_dart(l, i);

    long m_edges = (long)KB * G * DEG;
    printf("%d %ld\n", N, m_edges);
    for (int v = 0; v < KB * G; v++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", v, nbr[(size_t)l * N + v]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C: bi-lift annealing over semidirect and affine groups.
    elapsed = time.monotonic() - start
    c_budget = min(0.8 * time_limit, time_limit - 10.0 - elapsed)
    if d >= 2 and c_budget >= 2.0:
        tmo = min(c_budget + 6.0, time_limit - (time.monotonic() - start) - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best_n],
                            timeout=max(1.0, tmo))
            consider(*lib.parse_graph_text(out))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

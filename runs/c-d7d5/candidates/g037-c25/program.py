import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as the safe fallback).
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
# C engine: exhaustive-cost simulated annealing over metacyclic bi-Cayley graphs.
#
# Group G = Z_m x|_r Z_k (order M = m*k, element (a,b) coded a*k+b).
# Graph: A_x ~ B_{x*s} for s in S, |S| = d, with identity fixed in S (WLOG by
# relabelling B). Left multiplication is an automorphism, so the diameter
# condition reduces to two BFS runs: from A_1 and from B_1, each must reach every
# vertex within D steps. Cost = number of unreached vertices in both BFS.
# Cost 0 means a valid graph with 2M vertices.
# Groups are scanned in a window just above the best valid order found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef struct { int m, k, r; } Grp;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int dg = 3, DD = 3;
static double deadline = 0.0;

static Grp *grps = NULL;
static long ngrp = 0, gcap = 0;
static long *bstart = NULL, *bcount = NULL;

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void add_grp(int m, int k, int r) {
    if (ngrp >= gcap) {
        gcap = gcap ? gcap * 2 : 4096;
        grps = realloc(grps, sizeof(Grp) * (size_t)gcap);
        if (!grps) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
    }
    grps[ngrp].m = m;
    grps[ngrp].k = k;
    grps[ngrp].r = r;
    ngrp++;
}

static void enum_groups(int lo, int hi) {
    bstart = calloc((size_t)hi + 2, sizeof(long));
    bcount = calloc((size_t)hi + 2, sizeof(long));
    if (!bstart || !bcount) {
        fprintf(stderr, "oom\n");
        exit(1);
    }
    for (int M = lo; M <= hi; M++) {
        bstart[M] = ngrp;
        for (int k = 1; k <= M; k++) {
            if (M % k) continue;
            int m = M / k;
            if (m == 1) {
                add_grp(1, k, 0);
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcdll(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                add_grp(m, k, r);
            }
        }
        bcount[M] = ngrp - bstart[M];
    }
}

static int GM = 1, GK = 1, GO = 1;
static int *gpw = NULL, *mt = NULL, *ivt = NULL;
static int gpwcap = 0, ivcap = 0;
static long mtcap = 0;

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpw[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void set_group(Grp g) {
    GM = g.m;
    GK = g.k;
    GO = GM * GK;
    if (GK > gpwcap) {
        free(gpw);
        gpw = malloc(sizeof(int) * (size_t)GK);
        gpwcap = GK;
        if (!gpw) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
    }
    long long p = 1 % GM;
    for (int b = 0; b < GK; b++) {
        gpw[b] = (int)p;
        p = (p * g.r) % GM;
    }
    if ((long)GO * GO > mtcap) {
        free(mt);
        mtcap = (long)GO * GO;
        mt = malloc(sizeof(int) * (size_t)mtcap);
        if (!mt) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
    }
    if (GO > ivcap) {
        free(ivt);
        ivcap = GO;
        ivt = malloc(sizeof(int) * (size_t)ivcap);
        if (!ivt) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
    }
    for (int x = 0; x < GO; x++)
        for (int y = 0; y < GO; y++)
            mt[(long)x * GO + y] = gmul(x, y);
    for (int x = 0; x < GO; x++) {
        ivt[x] = 0;
        for (int y = 0; y < GO; y++) {
            if (mt[(long)x * GO + y] == 0) {
                ivt[x] = y;
                break;
            }
        }
    }
}

static int *Sx = NULL, *Sinv = NULL;
static int *vis = NULL, *qu = NULL;
static int vstamp = 0;
static long vcap = 0;

static void ensure_work(void) {
    if (!Sx) {
        Sx = malloc(sizeof(int) * (size_t)dg);
        Sinv = malloc(sizeof(int) * (size_t)dg);
        if (!Sx || !Sinv) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
    }
    if (2L * GO > vcap) {
        free(vis);
        free(qu);
        vcap = 2L * GO;
        vis = calloc((size_t)vcap, sizeof(int));
        qu = malloc(sizeof(int) * (size_t)vcap);
        vstamp = 0;
        if (!vis || !qu) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
    }
}

/* Number of nodes reached from src within DD steps. Nodes 0..GO-1 are A, GO..2GO-1 are B. */
static int reach(int src) {
    vstamp++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = vstamp;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = qu[head++];
            if (u < GO) {
                int base = u * GO;
                for (int t = 0; t < dg; t++) {
                    int v = GO + mt[base + Sx[t]];
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qu[tail++] = v;
                    }
                }
            } else {
                int base = (u - GO) * GO;
                for (int t = 0; t < dg; t++) {
                    int v = mt[base + Sinv[t]];
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
    }
    return tail;
}

static int eval_cost(void) {
    int N2 = 2 * GO;
    int a = N2 - reach(0);
    int b = N2 - reach(GO);
    return a + b;
}

static int in_set(int e) {
    for (int j = 0; j < dg; j++)
        if (Sx[j] == e) return 1;
    return 0;
}

/* Annealing over S (S[0] = identity fixed). Writes best S to outS, returns its cost. */
static int sa_run(long iters, int *outS) {
    for (int j = 0; j < dg; j++) Sx[j] = -1;
    Sx[0] = 0;
    for (int t = 1; t < dg; t++) {
        int e;
        do {
            e = 1 + rint_(GO - 1);
        } while (in_set(e));
        Sx[t] = e;
    }
    for (int t = 0; t < dg; t++) Sinv[t] = ivt[Sx[t]];
    int cur = eval_cost();
    int best = cur;
    memcpy(outS, Sx, sizeof(int) * (size_t)dg);
    for (long it = 0; it < iters && best > 0; it++) {
        if ((it & 255) == 0 && now_s() > deadline) break;
        double T = 1.5 * (1.0 - (double)it / (double)iters) + 0.05;
        int t = 1 + rint_(dg - 1);
        int old = Sx[t], oldinv = Sinv[t];
        int e;
        do {
            e = 1 + rint_(GO - 1);
        } while (in_set(e));
        Sx[t] = e;
        Sinv[t] = ivt[e];
        int nc = eval_cost();
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(outS, Sx, sizeof(int) * (size_t)dg);
            }
        } else {
            Sx[t] = old;
            Sinv[t] = oldinv;
        }
    }
    return best;
}

int main(int argc, char **argv) {
    dg = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int lo = argc > 5 ? atoi(argv[5]) : dg + 1;
    int hi = argc > 6 ? atoi(argv[6]) : lo + 1;

    if (dg < 2 || DD < 1 || lo < dg + 1 || hi < lo || hi > 4000) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 4; i++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    enum_groups(lo, hi);

    int *outS = malloc(sizeof(int) * (size_t)dg);
    int *saved = malloc(sizeof(int) * (size_t)dg);
    if (!outS || !saved) {
        printf("0 0\n");
        return 0;
    }

    long base = (long)lo - 1;   /* best valid order found so far (frontier) */
    int have = 0;
    Grp bestG = {1, 1, 0};
    const int W = 8;
    const long ITERS = 15000;

    while (now_s() < deadline) {
        long M = base + 1 + rint_(W);
        if (M > hi) {
            M = hi;
            if (M <= base) break;
        }
        if (bcount[M] == 0) continue;
        Grp g = grps[bstart[M] + rint_((int)bcount[M])];
        set_group(g);
        ensure_work();
        int c = sa_run(ITERS, outS);
        if (c == 0) {
            base = M;
            have = 1;
            bestG = g;
            memcpy(saved, outS, sizeof(int) * (size_t)dg);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestG);
    ensure_work();
    memcpy(Sx, saved, sizeof(int) * (size_t)dg);
    int n = 2 * GO;
    long m = (long)dg * GO;
    printf("%d %ld\n", n, m);
    for (int x = 0; x < GO; x++)
        for (int t = 0; t < dg; t++)
            printf("%d %d\n", x, GO + mt[(long)x * GO + Sx[t]]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the group-based annealing.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

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

    if D < 3 or d < 3:
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Metacyclic bi-Cayley search: group orders M in [lo, hi] give graphs on 2M vertices.
    c_budget = deadline - time.monotonic() - 1.0
    if c_budget >= 2.0:
        moore = lib.moore_bound(d, D)
        lo = max(d + 1, moore // 8)
        hi = min(2000, moore // 2)
        if lo <= hi:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", lo, hi],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

"""Group-lift ladder search for bipartite degree-diameter graphs.

This version replaces the earlier hill-climb with a different construction. The C engine
enumerates every metacyclic group Z_m x|_r Z_k of order N (cyclic, dihedral, and the
other semidirect products). For each target order s = 2pN it searches over base multigraphs
on p + p fibres (p <= 4) and over group voltages, using simulated annealing. Each lift is a
regular bipartite graph. Left multiplication by the group is an automorphism, so the
diameter test only needs BFS from the 2p fibre representatives.

The C engine climbs the target orders s upward from the current best and gives each order a
time slice that adapts to the time left. The Python side keeps the algebraic starts
(K_{d,d}, projective plane incidence, Araujo-Pardo-Lopez, W(q)) as a fallback, and it only
accepts the C result after lib.is_valid confirms it.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Group-lift ladder search for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit [start_size]
 * stdin is ignored. stdout: "n m" then m lines "u v" for the largest valid lift found,
 * or "0 0" if none was found.
 *
 * A lift has p A-fibres and p B-fibres, each a copy of a group G of order N. Dart (i,j,g) joins
 * (A,i,x) to (B,j,x*g). The base multigraph is d-regular on p+p vertices, and darts sharing a
 * fibre pair have distinct voltages, so the lift is simple and d-regular.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXV 2048
#define MAXD 32
#define MAXP 4
#define MAXDART (MAXD * MAXP)
#define MAXCAND 256

static int d, D;
static double t_deadline;

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

static int gcd_i(int a, int b) {
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
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */
static int GM, GK, GR, NN;
static int GRP[MAXN];

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; NN = m * k;
    GRP[0] = 1 % m;
    for (int b = 1; b < k; b++) GRP[b] = (int)((long)GRP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)GRP[b] * c) % GM) * GK + (b + e) % GK;
}

/* Current lift state. */
static int P;
static int nd;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];
static int adjv[MAXV][MAXD];
static int degv[MAXV];
static int VV;
static unsigned seen[MAXV], stamp = 0;
static int qb[MAXV], dist[MAXV];

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Pick a voltage for dart t that differs from the other darts on the same fibre pair. */
static int fresh_g(int t) {
    for (;;) {
        int g = rndint(NN), ok = 1;
        for (int u = 0; u < nd; u++)
            if (u != t && dI[u] == dI[t] && dJ[u] == dJ[t] && dG[u] == g) { ok = 0; break; }
        if (ok) return g;
    }
}

/* Random d-regular connected base multigraph on P + P vertices, with fresh voltages. */
static int random_base(void) {
    for (int tries = 0; tries < 200; tries++) {
        int M2[MAXP][MAXP];
        memset(M2, 0, sizeof M2);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            shuffle_int(perm, P);
            for (int i = 0; i < P; i++) M2[i][perm[i]]++;
        }
        int sb[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        sb[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * P; u++) {
                if (sb[u]) continue;
                int linked = v < P ? (u >= P && M2[v][u - P]) : (u < P && M2[u][v - P]);
                if (linked) { sb[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * P) {
            nd = 0;
            for (int i = 0; i < P; i++)
                for (int j = 0; j < P; j++)
                    for (int c = 0; c < M2[i][j]; c++) {
                        dI[nd] = i; dJ[nd] = j; dG[nd] = 0; nd++;
                    }
            for (int t = 0; t < nd; t++) dG[t] = fresh_g(t);
            return 1;
        }
    }
    return 0;
}

static void build(void) {
    VV = 2 * P * NN;
    for (int v = 0; v < VV; v++) degv[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NN; x++) {
            int A = dI[t] * NN + x;
            int B = (P + dJ[t]) * NN + gmul(x, dG[t]);
            adjv[A][degv[A]++] = B;
            adjv[B][degv[B]++] = A;
        }
}

/* Orbit-reduced cost: pairs at distance > D, counted by BFS from the 2P fibre representatives.
 * Left multiplication is an automorphism, so this is zero exactly when the lift has diameter <= D. */
static long eval(void) {
    build();
    long bad = 0;
    for (int b = 0; b < 2 * P; b++) {
        int src = b * NN;
        stamp++;
        int h = 0, t = 0;
        seen[src] = stamp;
        dist[src] = 0;
        qb[t++] = src;
        while (h < t) {
            int v = qb[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < degv[v]; i++) {
                int u = adjv[v][i];
                if (seen[u] != stamp) {
                    seen[u] = stamp;
                    dist[u] = dist[v] + 1;
                    qb[t++] = u;
                }
            }
        }
        bad += VV - t;
    }
    return bad;
}

/* One annealing attempt with a fresh random base. Returns 1 if a valid lift is in the state. */
static int attempt(int steps, double dl) {
    if (!random_base()) return 0;
    long cur = eval();
    double T = 1.0;
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 511) == 0 && now() > dl) break;
        int t = rndint(nd);
        int old = dG[t];
        dG[t] = fresh_g(t);
        long nb = eval();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
        else dG[t] = old;
        T *= 0.999;
        if (T < 0.05) T = 1.0;
    }
    return cur == 0;
}

typedef struct { int p, m, k, r; } Cand;
#define NCAND_MAX MAXCAND
static Cand cands[NCAND_MAX];
static int ncand;

static void push_cand(int p, int m, int k, int r) {
    if (ncand < NCAND_MAX) {
        cands[ncand].p = p;
        cands[ncand].m = m;
        cands[ncand].k = k;
        cands[ncand].r = r;
        ncand++;
    }
}

/* All semidirect groups Z_m x|_r Z_k of order N, paired with base size p. */
static void add_groups(int p, int N) {
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { push_cand(p, 1, k, 0); continue; }
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k, m) == 1 % m) push_cand(p, m, k, r);
    }
}

static int have_best = 0;
static long best_size;
static int bP, bM, bK, bR, bNd;
static int bI[MAXDART], bJ[MAXDART], bG[MAXDART];

static void save_best(long size) {
    have_best = 1;
    best_size = size;
    bP = P; bM = GM; bK = GK; bR = GR; bNd = nd;
    for (int t = 0; t < nd; t++) {
        bI[t] = dI[t]; bJ[t] = dJ[t]; bG[t] = dG[t];
    }
}

/* Try to find a lift of order s (= 2 P N). Returns 1 on success. */
static int try_size(long s, double dl) {
    ncand = 0;
    for (int p = 1; p <= MAXP; p++) {
        if (s % (2 * p)) continue;
        long N = s / (2 * p);
        if (N < d || N > MAXN) continue;
        add_groups(p, (int)N);
    }
    if (!ncand) return 0;
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = cands[i]; cands[i] = cands[j]; cands[j] = tmp;
    }
    while (now() < dl) {
        for (int c = 0; c < ncand; c++) {
            if (now() >= dl) return 0;
            Cand *cd = &cands[c];
            set_group(cd->m, cd->k, cd->r);
            P = cd->p;
            if (attempt(6000, dl)) {
                save_best((long)2 * P * NN);
                return 1;
            }
        }
    }
    return 0;
}

static void print_best(void) {
    P = bP;
    set_group(bM, bK, bR);
    nd = bNd;
    for (int t = 0; t < nd; t++) {
        dI[t] = bI[t]; dJ[t] = bJ[t]; dG[t] = bG[t];
    }
    build();
    long m = (long)P * NN * d;
    printf("%d %ld\n", VV, m);
    for (int u = 0; u < P * NN; u++)
        for (int i = 0; i < degv[u]; i++)
            printf("%d %d\n", u, adjv[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_size]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long s0 = argc > 5 ? atol(argv[5]) : 2L * d;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_deadline = t0 + limit * 0.95;

    long moore = moore_bound();
    if (moore > MAXV) moore = MAXV;
    if (s0 < 2L * d) s0 = 2L * d;
    if (s0 % 2) s0++;

    for (long s = s0; s <= moore; s += 2) {
        double tn = now();
        if (tn >= t_deadline) break;
        long remaining = (moore - s) / 2 + 1;
        double per = (t_deadline - tn) / (double)remaining;
        if (per < 0.02) per = 0.02;
        if (per > 4.0) per = 4.0;
        try_size(s, tn + per);
    }

    if (have_best) print_best();
    else printf("0 0\n");
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), best[0] + 2],
                         stdin_graph=None, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best

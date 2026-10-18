"""Bi-Cayley lift search with iterated local search (ILS) in C, plus algebraic fallbacks.

Changed from the parent: the parent annealed random lifts with single-coordinate
moves. This version uses a different search. Each step samples NCAND candidate
moves (a layer-permutation swap or a voltage change), applies the best one even if
it is worse, keeps a snapshot of the best state, and perturbs after PATIENCE
non-improving steps. Groups are direct or semidirect products Z_m x| Z_k2 with
k2 in {1,2,3,4,5,6,8,10,12}. Every lift is a regular cover of a 2K-vertex base, so
the reachability bitmasks from the 2K block representatives decide diameter.

Safety: K_{d,d}, the projective-plane incidence graph, the Araujo-Lopez graph and
W(q) (for D = 4) are built first. Every candidate is checked with lib.is_valid
before it is kept, and the returned graph is validated again at the end.
"""
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
#include <time.h>

#define MAXD 16
#define MAXK 6
#define MAXN 24000
#define PEN 1000
#define NCAND 12
#define PATIENCE 300

typedef uint64_t u64;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int GM, GK, GG;
static long long GR;
static long long PW[64];

static void set_group(int m, int k2, long long r) {
    GM = m; GK = k2; GG = m * k2; GR = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { PW[b] = p; p = (p * r) % m; }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long long t = ((long long)a + PW[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long long t = (PW[nb] * a) % GM;
    long long na = (GM - t) % GM;
    return (int)(na * GK + nb);
}

/* Lift state. nbr[l*N + v] is the layer-l neighbour of v. */
static int DEG, DD, K, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD * MAXN];
static u64 bufA[MAXN], bufB[MAXN];
static u64 FULL;

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int sinv = ginv(s);
    int q = K + p;
    int *nl = nbr + (size_t)l * N;
    for (int g = 0; g < GG; g++) nl[i * GG + g] = q * GG + gmul(g, s);
    for (int h = 0; h < GG; h++) nl[q * GG + h] = i * GG + gmul(h, sinv);
}

/* Cost = unreached (representative, vertex) pairs + PEN * duplicated darts. */
static long long eval(void) {
    u64 *x = bufA, *y = bufB;
    for (int v = 0; v < N; v++) x[v] = 0;
    for (int b = 0; b < 2 * K; b++) x[b * GG] |= (u64)1 << b;
    for (int r = 0; r < DD; r++) {
        int ch = 0;
        for (int v = 0; v < N; v++) {
            u64 u = x[v];
            for (int l = 0; l < DEG; l++) u |= x[nbr[l * N + v]];
            y[v] = u;
            if (u != x[v]) ch = 1;
        }
        u64 *t = x; x = y; y = t;
        if (!ch) break;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += pc64(FULL & ~x[v]);
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    return unr + (long long)PEN * dup;
}

/* A move is an involution: applying it twice restores the state. */
typedef struct { int type, l, i1, i2, val; } Mv;

static void do_mv(Mv *m) {
    if (m->type == 0) {
        int t = layers[m->l][m->i1];
        layers[m->l][m->i1] = layers[m->l][m->i2];
        layers[m->l][m->i2] = t;
        set_dart(m->l, m->i1);
        set_dart(m->l, m->i2);
    } else {
        int t = S[m->l][m->i1];
        S[m->l][m->i1] = m->val;
        m->val = t;
        set_dart(m->l, m->i1);
    }
}

static Mv rand_mv(void) {
    Mv m;
    if (K >= 2 && rndu() < 0.3) {
        m.type = 0;
        m.l = rndint(DEG);
        m.i1 = rndint(K);
        m.i2 = rndint(K - 1);
        if (m.i2 >= m.i1) m.i2++;
        m.val = 0;
    } else {
        m.type = 1;
        m.l = rndint(DEG);
        m.i1 = rndint(K);
        m.i2 = 0;
        m.val = rndint(GG);
    }
    return m;
}

static int snapL[MAXD][MAXK], snapS[MAXD][MAXK];

static void snap(void) {
    memcpy(snapL, layers, sizeof(layers));
    memcpy(snapS, S, sizeof(S));
}

static void restore(void) {
    memcpy(layers, snapL, sizeof(layers));
    memcpy(S, snapS, sizeof(S));
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int bestN = 0, bestM = 0;
static int *bestE = NULL;

static void record(void) {
    int m = K * GG * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int idx = 0;
    for (int u = 0; u < K * GG; u++)
        for (int l = 0; l < DEG; l++) {
            e[2 * idx] = u;
            e[2 * idx + 1] = nbr[l * N + u];
            idx++;
        }
    free(bestE);
    bestE = e;
    bestM = m;
    bestN = N;
}

/* Iterated local search: sampled best-of-NCAND moves, snapshot of the best state,
   and a perturbation after PATIENCE steps without improvement. */
static int ils(double deadline) {
    long long cur = eval();
    long long bestc = cur;
    int stall = 0;
    snap();
    while (cur > 0) {
        if (now() > deadline) break;
        Mv best;
        long long bc = -1;
        int nb = 0;
        for (int c = 0; c < NCAND; c++) {
            Mv m = rand_mv();
            do_mv(&m);
            long long v = eval();
            do_mv(&m);
            if (bc < 0 || v < bc) { bc = v; best = m; nb = 1; }
            else if (v == bc) { nb++; if (rndint(nb) == 0) best = m; }
        }
        do_mv(&best);
        cur = bc;
        if (cur < bestc) { bestc = cur; snap(); stall = 0; }
        else stall++;
        if (stall > PATIENCE) {
            restore();
            for (int p = 0; p < 3; p++) { Mv m = rand_mv(); do_mv(&m); }
            cur = eval();
            stall = 0;
        }
    }
    return cur == 0;
}

static const int K2L[10] = {1, 2, 2, 3, 4, 5, 6, 8, 10, 12};

static void sample_group(int target, int *pm, int *pk, long long *pr) {
    int k2 = K2L[rndint(10)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    long long r = 1;
    if (k2 > 1 && m > 2 && rndu() < 0.8) {
        for (int t = 0; t < 80; t++) {
            long long c = 2 + rndint(m - 2);
            if (gcdll(c, m) == 1 && pmod(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    *pm = m; *pk = k2; *pr = r;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    DD = D;
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)seed * 2654435761ULL + 977ULL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    double t0 = now(), deadline = t0 + tl;
    int bestn = n0;
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < deadline) {
        int k;
        if (rndu() < 0.25) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double s = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.05 * rndu();
                if (s > bs) { bs = s; k = kk; }
            }
        }
        int base = bestn / (2 * k);
        int target = base + 1 + rndint(base / 10 + 2);
        if (target < 2) target = 2;

        int m, k2;
        long long r;
        sample_group(target, &m, &k2, &r);
        set_group(m, k2, r);
        K = k;
        N = 2 * K * GG;
        if (N <= bestn || N > MAXN) continue;
        FULL = (((u64)1) << (2 * K)) - 1;

        for (int l = 0; l < DEG; l++) {
            for (int i = 0; i < K; i++) layers[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = t;
            }
        }
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) S[l][i] = rndint(GG);
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) set_dart(l, i);

        trials[K]++;
        double tdead = now() + tl * 0.3;
        if (tdead > deadline) tdead = deadline;
        if (ils(tdead)) {
            wins[K]++;
            if (N > bestn) { bestn = N; record(); }
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", bestN, bestM);
        for (int j = 0; j < bestM; j++)
            printf("%d %d\n", bestE[2 * j], bestE[2 * j + 1]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Algebraic baselines.
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
# Slack extension: add vertices using spare degree; every kept graph is valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                ol = lib.araujo_lopez_graph(d - 2)
                consider(ol[0], ol[1])
            except Exception:
                pass

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main engine: C iterated local search over bi-Cayley lifts, seeded with the best order.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    remaining = t0 + budget - time.monotonic()
    if remaining > 3.0 and d >= 2:
        c_tl = round(remaining - 1.0, 2)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, c_tl, best_n],
                            stdin_graph=None, timeout=c_tl + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Use spare degree in the best graph to add vertices, if time allows.
    rng = random.Random(seed)
    final_deadline = t0 + max(1.0, time_limit - 6.0)
    if time.monotonic() < final_deadline - 1.0:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 6
#define GMAX 2000
#define MAXCAND 40000
#define ILS_ROUNDS 4

typedef struct { int m, k2, r; } cand_t;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int lbest[MAXD][MAXK], vbest[MAXD][MAXK];
static long long run_cost = 0;
static int *bE = NULL;
static int bEc = 0, bestN = 0, haveBest = 0;
static int trials[MAXK + 1], wins[MAXK + 1];
static cand_t cands[MAXCAND];
static int ncand = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e), needs r^k2 = 1 mod m. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX || G < 1) return 0;
    G_ = G;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pw = malloc(sizeof(int) * k2);
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    /* RS[s][h] = g with g*s = h. */
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pw);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * N);
    tmpr = malloc(sizeof(u64) * N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static void apply_all(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++)
            setdart(l, i, lay[l][i], VS[l][i]);
}

static void save_state(void) {
    memcpy(lbest, lay, sizeof lay);
    memcpy(vbest, VS, sizeof VS);
}

static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[(size_t)l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

/* Random layer permutations and random voltages. */
static void random_state(void) {
    int k = K_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    apply_all();
}

/* Iterated-local-search kick: re-randomise a few voltages. */
static void perturb(int p) {
    for (int q = 0; q < p; q++) {
        int l = rndi(d_), i = rndi(K_);
        VS[l][i] = rndi(G_);
        setdart(l, i, lay[l][i], VS[l][i]);
    }
}

/* Simulated annealing over layers and voltages. Leaves the state at cost 0 on success,
   and lbest/vbest holds the best state of this run with cost run_cost. */
static int search(double tend, int iters, int patience, double tf) {
    int k = K_, d = d_, G = G_, N = N_;
    u64 full = (1ULL << (2 * k)) - 1;
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    int last = 0;
    save_state();
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > tend) break;
        double temp = tf * c0 * (1.0 - (double)t / iters);
        if (temp < 0.4) temp = 0.4;
        if (k >= 2 && rndu() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            setdart(l, i1, t2, VS[l][i1]);
            setdart(l, i2, t1, VS[l][i2]);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                setdart(l, i1, t1, VS[l][i1]);
                setdart(l, i2, t2, VS[l][i2]);
            }
        } else {
            int l = rndi(d), i = rndi(k);
            /* Defect-targeted choice: aim at a random unreached vertex (uses the last evaluation). */
            if (rndu() < 0.4) {
                int v = -1;
                for (int tr = 0; tr < 8; tr++) {
                    int c = rndi(N);
                    if (rch[c] != full) { v = c; break; }
                }
                if (v >= 0) {
                    int blk = v / G;
                    if (blk < k) i = blk;
                    else {
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == blk - k) { i = ii; break; }
                    }
                }
            }
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            setdart(l, i, lay[l][i], nw);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                VS[l][i] = old;
                setdart(l, i, lay[l][i], old);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; save_state(); }
    }
    run_cost = bestc;
    return cost == 0;
}

/* New routine: iterated local search. Restarts from the best state of the previous
   run (lbest) with a few random voltage kicks, and keeps the best base seen. */
static int ils(double tend) {
    static int bl[MAXD][MAXK], bv[MAXD][MAXK];
    long long bcost = run_cost;
    memcpy(bl, lbest, sizeof lbest);
    memcpy(bv, vbest, sizeof vbest);
    for (int round = 0; round < ILS_ROUNDS && now() < tend; round++) {
        memcpy(lay, bl, sizeof lay);
        memcpy(VS, bv, sizeof VS);
        apply_all();
        perturb(2 + rndi(3));
        int ok = search(tend, 8000, 1500, 0.01);
        if (ok) return 1;
        if (run_cost <= bcost) {
            bcost = run_cost;
            memcpy(bl, lbest, sizeof lbest);
            memcpy(bv, vbest, sizeof vbest);
        }
    }
    return 0;
}

/* New routine: systematic enumeration of all semidirect groups of order G,
   including cyclic (m = 1 or k2 = 1) cases. */
static void gen_cands(int G) {
    ncand = 0;
    for (int k2 = 1; k2 <= G; k2++) {
        if (G % k2) continue;
        int m = G / k2;
        if (m == 1) {
            if (ncand < MAXCAND) { cands[ncand].m = 1; cands[ncand].k2 = k2; cands[ncand].r = 0; ncand++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            if (ncand < MAXCAND) { cands[ncand].m = m; cands[ncand].k2 = k2; cands[ncand].r = r; ncand++; }
        }
    }
}

static int pick_k(void) {
    if (rndu() < 0.2) return 1 + rndi(MAXK);
    double bs = -1.0;
    int bk = 1;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rndu();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

static void extract(void) {
    int kG = K_ * G_, d = d_, N = N_;
    int cnt = kG * d;
    int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
    int p = 0;
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < d; l++) {
            ne[2 * p] = u;
            ne[2 * p + 1] = nb[(size_t)l * N + u];
            p++;
        }
    free(bE);
    bE = ne;
    bEc = cnt;
    bestN = N;
    haveBest = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = (argc > 5) ? atoi(argv[5]) : 2;
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    bestN = minN - 1;   /* accept only graphs with more vertices than this */

    while (now() < tend) {
        int k = pick_k();
        int Gmin = bestN / (2 * k) + 1;          /* need 2*k*G > bestN */
        int W = Gmin / 6 + 3;
        int G = Gmin + rndi(W);
        if (G < 1 || G > GMAX) continue;
        gen_cands(G);
        if (ncand == 0) continue;
        cand_t c = cands[rndi(ncand)];
        if (!build_group(c.m, c.k2, c.r)) continue;
        K_ = k;
        alloc_state(2 * k * G_);
        trials[k]++;
        random_state();
        int ok = search(tend, 20000, 3000, 0.02);
        if (!ok && run_cost < 1000 && run_cost <= N_ / 4 && now() < tend)
            ok = ils(tend);
        if (ok) {
            wins[k]++;
            if (N_ > bestN) extract();
        }
    }

    if (!haveBest) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for degree d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
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
# Main build: exact constructions first, then the C bi-Cayley search
# (bandit over base size k, systematic semidirect group enumeration,
# iterated local search), then slack extension.
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum
        try:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])
        except Exception:
            pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Use any spare degree in the best graph to add vertices (cheap, time-bounded).
    rng = random.Random(seed)
    try:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, start + time_limit - 5.0)
        consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

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
#define MAXK 8
#define GMAX 2000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
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
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    G_ = G;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
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

static void apply_dart(int l, int i) { setdart(l, i, lay[l][i], VS[l][i]); }

static void snapshot(void) {
    memcpy(BL, lay, sizeof lay);
    memcpy(BV, VS, sizeof VS);
}

static void restore_snapshot(void) {
    int d = d_, k = K_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) { lay[l][i] = BL[l][i]; VS[l][i] = BV[l][i]; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
}

/* Cost = unreached (representative, vertex) pairs + heavy penalty for duplicate darts. */
static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
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

/* Simulated annealing with iterated-local-search kicks from the best state.
   Returns 1 when a valid graph (cost 0) is in the current state. */
static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_, N = N_;
    u64 full = (1ULL << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    snapshot();
    int last = 0, kicks = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            restore_snapshot();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                VS[l][i] = rndi(G);
                apply_dart(l, i);
            }
            cost = evalcost();
            if (cost < bestc) { bestc = cost; snapshot(); }
            last = t;
            continue;
        }
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rndu() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            apply_dart(l, i1);
            apply_dart(l, i2);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                apply_dart(l, i1);
                apply_dart(l, i2);
            }
        } else {
            /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.4) {
                int start = rndi(N), v = -1;
                for (int q = 0; q < N; q++) {
                    int w = (start + q) % N;
                    if (rch[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndi(d);
                    if (b < k) i = b;
                    else {
                        int jb = b - k;
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == jb) { i = ii; break; }
                        if (i < 0) i = rndi(k);
                    }
                    picked = 1;
                }
            }
            if (!picked) { l = rndi(d); i = rndi(k); }
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            apply_dart(l, i);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                VS[l][i] = old;
                apply_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; snapshot(); }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < tend) {
        int k = Ks[rndi(10)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 30 + 3);
        int k2 = K2s[rndi(13)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        K_ = k;
        alloc_state(2 * k * G_);
        int ok = search(tend, 20000, 3000, 6);
        if (ok && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = u;
                    ne[2 * p + 1] = nb[(size_t)l * N_ + u];
                    p++;
                }
            free(bE);
            bE = ne;
            bEc = cnt;
            bestN = N_;
            minN = N_ + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


# Haar-type bi-Cayley engine: vertices A_g = g and B_g = G + g, A_g ~ B_{g s} for s in S (|S| = d).
# Input graph on stdin is the multiplication table of a group G (identity = 0): pair index x*G+y
# carries (x, x*y). Searches S by annealing; cost = vertices unreached within D from A_0 and B_0
# (left translation is an automorphism, so these two sources suffice).
HAAR_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int G, D, d;
static int *M, *INV, *S, *Q, *stamp;
static char *inS;
static int curstamp = 0;

static int unreached(int src) {
    curstamp++;
    int head = 0, tail = 0;
    Q[tail++] = src;
    stamp[src] = curstamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int levelEnd = tail;
        while (head < levelEnd) {
            int v = Q[head++];
            if (v < G) {
                const int *row = M + (size_t)v * G;
                for (int i = 0; i < d; i++) {
                    int u = G + row[S[i]];
                    if (stamp[u] != curstamp) { stamp[u] = curstamp; Q[tail++] = u; }
                }
            } else {
                const int *row = M + (size_t)(v - G) * G;
                for (int i = 0; i < d; i++) {
                    int u = row[INV[S[i]]];
                    if (stamp[u] != curstamp) { stamp[u] = curstamp; Q[tail++] = u; }
                }
            }
        }
    }
    return 2 * G - tail;
}

static int cost(void) { return unreached(0) + unreached(G); }

static void randomS(void) {
    memset(inS, 0, (size_t)G);
    for (int i = 0; i < d; i++) {
        int x;
        do x = rndi(G); while (inS[x]);
        inS[x] = 1;
        S[i] = x;
    }
}

static int search(double tend, int *bestS) {
    const long long chunk = 4000;
    while (now() < tend) {
        randomS();
        int cur = cost();
        if (cur == 0) { memcpy(bestS, S, sizeof(int) * (size_t)d); return 1; }
        for (long long t = 0; t < chunk; t++) {
            if ((t & 127) == 0 && now() > tend) return 0;
            double T = 4.0 * pow(0.05, (double)t / (double)chunk);
            int i = rndi(d);
            int old = S[i], nw;
            do nw = rndi(G); while (inS[nw]);
            inS[old] = 0; inS[nw] = 1; S[i] = nw;
            int c2 = cost();
            if (c2 <= cur || rndu() < exp((double)(cur - c2) / T)) {
                cur = c2;
                if (cur == 0) { memcpy(bestS, S, sizeof(int) * (size_t)d); return 1; }
            } else {
                inS[nw] = 0; inS[old] = 1; S[i] = old;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 2 || m != n * n || d < 1 || d >= n || D < 1) { printf("0 0\n"); return 0; }
    G = n;
    M = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    for (long long i = 0; i < m; i++) {
        int x, y;
        if (scanf("%d %d", &x, &y) != 2) { printf("0 0\n"); return 0; }
        M[i] = y;
    }
    for (int y = 0; y < G; y++)
        if (M[y] != y || M[(size_t)y * G] != y) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++)
            if (M[(size_t)x * G + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) { printf("0 0\n"); return 0; }
    }
    S = malloc(sizeof(int) * (size_t)d);
    int *bestS = malloc(sizeof(int) * (size_t)d);
    inS = malloc((size_t)G);
    Q = malloc(sizeof(int) * (size_t)2 * G);
    stamp = calloc((size_t)2 * G, sizeof(int));

    double tend = now() + tl;
    if (!search(tend, bestS)) { printf("0 0\n"); return 0; }

    printf("%d %d\n", 2 * G, G * d);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, G + M[(size_t)g * G + bestS[i]]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------- group constructions

def _pmul(a, b):
    """Composition of permutations given as tuples."""
    return tuple([a[i] for i in b])


def _finish(gens, mul, ident, cap=800):
    """Closure of gens under mul; identity is index 0. Returns (elems, idx, mul) or None if too big."""
    elems = [ident]
    idx = {ident: 0}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in idx:
                    if len(elems) >= cap:
                        return None
                    idx[y] = len(elems)
                    elems.append(y)
                    new.append(y)
        frontier = new
    return elems, idx, mul


def _psl_pgl(q, pgl):
    """PSL(2,q) or PGL(2,q) acting on the projective line (points 0..q-1 and inf = q)."""
    F = lib.GF(q)
    inf = q
    gens = [tuple([F.add(x, b) for x in range(q)] + [inf]) for b in range(q)]
    scales = range(1, q) if pgl else sorted({F.mul(x, x) for x in range(1, q)})
    gens += [tuple([F.mul(a, x) for x in range(q)] + [inf]) for a in scales]
    gens.append(tuple([inf] + [F.neg(F.inv(x)) for x in range(1, q)] + [0]))
    return gens, _pmul, tuple(range(q + 1))


def _affine(q):
    """AGL(1,q) acting on GF(q)."""
    F = lib.GF(q)
    w = F.primitive_element()
    gens = [tuple([F.add(x, b) for x in range(q)]) for b in range(q)]
    gens.append(tuple([F.mul(w, x) for x in range(q)]))
    return gens, _pmul, tuple(range(q))


def _heis(p):
    """Heisenberg group of order p^3."""
    def mul(x, y):
        return ((x[0] + y[0]) % p, (x[1] + y[1]) % p, (x[2] + y[2] + x[0] * y[1]) % p)
    return [(1, 0, 0), (0, 1, 0), (0, 0, 1)], mul, (0, 0, 0)


def _product(gens_b, mul_b, id_b, k):
    """Direct product of a group with Z_k."""
    gens = [(g, 0) for g in gens_b] + [(id_b, 1)]

    def mul(x, y):
        return (mul_b(x[0], y[0]), (x[1] + y[1]) % k)
    return gens, mul, (id_b, 0)


def _group_specs():
    """(order, thunk) pairs for candidate groups of order at most 800."""
    specs = []

    def add(order, thunk):
        if 2 < order <= 800:
            specs.append((order, thunk))

    for q in (5, 7, 9, 11):
        add(q * (q * q - 1) // 2, lambda q=q: _finish(*_psl_pgl(q, False)))
        add(q * (q * q - 1), lambda q=q: _finish(*_psl_pgl(q, True)))
    add(504, lambda: _finish(*_psl_pgl(8, False)))
    for q in (7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27):
        add(q * (q - 1), lambda q=q: _finish(*_affine(q)))
    for p in (3, 5, 7):
        add(p ** 3, lambda p=p: _finish(*_heis(p)))
    for q, pgl, base_order in ((5, False, 60), (5, True, 120), (7, False, 168),
                               (7, True, 336), (9, False, 360)):
        for k in range(2, 14):
            add(base_order * k,
                lambda q=q, pgl=pgl, k=k: _finish(*_product(*_psl_pgl(q, pgl), k)))
    return specs


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(0.5, min(0.85 * time_limit, time_limit - 8.0))
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
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    # Stage 1: the proven lift search (keeps the known-good level).
    remaining = deadline - time.monotonic()
    tp = 0.6 * remaining
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(tp, 2), best_n + 1],
                        timeout=tp + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: bi-Cayley (Haar-type) graphs over non-abelian groups of order > best_n / 2.
    hi = lib.moore_bound(d, D) // 2
    for order, thunk in sorted(_group_specs(), key=lambda s: s[0]):
        left = deadline - 1.0 - time.monotonic()
        if left < 2.0:
            break
        if not (best_n // 2 < order <= hi) or order <= d:
            continue
        try:
            grp = thunk()
        except Exception:
            grp = None
        if grp is None:
            continue
        elems, idx, mul = grp
        G = len(elems)
        if G <= d or 2 * G <= best_n:
            continue
        edges = [(i, idx[mul(x, y)]) for i, x in enumerate(elems) for y in elems]
        t_slice = min(left, max(4.0, 0.5 * left))
        try:
            out = lib.run_c(HAAR_SOURCE, [d, D, seed, round(t_slice, 2)],
                            stdin_graph=(G, edges), timeout=t_slice + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

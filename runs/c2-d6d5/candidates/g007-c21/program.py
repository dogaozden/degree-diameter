import itertools
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
#define MAXG 1000
#define MAXN 4000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Group G given by full multiplication table MT (identity = index 0).
   Lift: k A-blocks, k B-blocks, d layers; each layer is a matching
   A_i -> B_{lay[l][i]} with voltage VS[l][i]:  A_{i,g} ~ B_{j, g*s}.
   Vertices: A_{i,g} = i*G+g, B_{j,h} = (k+j)*G+h. Total N = 2*k*G. */
static int d_, D_, G, K_;
static int *MT = NULL, *INV = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int N_ = 0;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bestE = NULL;
static int bestEc = 0, bestN = 0;

static int read_group(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXG || m != n * n) return 0;
    G = n;
    MT = malloc(sizeof(int) * (size_t)m);
    INV = malloc(sizeof(int) * (size_t)n);
    for (int p = 0; p < m; p++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (v < 0 || v >= n) return 0;
        MT[p] = v;
    }
    for (int x = 0; x < n; x++) if (MT[x] != x) return 0;
    for (int x = 0; x < n; x++) if (MT[x * n] != x) return 0;
    for (int x = 0; x < n; x++) {
        INV[x] = -1;
        for (int y = 0; y < n; y++) if (MT[x * n + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    N_ = N;
}

static void setdart(int l, int i, int j, int s) {
    int N = N_, k = K_;
    int *row = nb + (size_t)l * N;
    int si = INV[s];
    for (int g = 0; g < G; g++)
        row[i * G + g] = (k + j) * G + MT[g * G + s];
    for (int h = 0; h < G; h++)
        row[(k + j) * G + h] = i * G + MT[h * G + si];
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

/* Cost = unreached (vertex, representative) pairs + heavy penalty for duplicate edges.
   By left-translation symmetry only the 2k identity vertices need to be sources. */
static long long evalcost(void) {
    int N = N_, k = K_, d = d_;
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

static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, N = N_;
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

static void store_best(int N) {
    int kG = K_ * G, d = d_;
    int cnt = kG * d;
    int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
    int p = 0;
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < d; l++) {
            ne[2 * p] = u;
            ne[2 * p + 1] = nb[(size_t)l * N + u];
            p++;
        }
    free(bestE);
    bestE = ne;
    bestEc = cnt;
    bestN = N;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 2 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (!read_group()) { printf("0 0\n"); return 0; }

    double tend = now() + tl;
    double slice = tl / 4.0;
    if (slice < 0.5) slice = 0.5;

    while (now() < tend) {
        int fk[MAXK], nf = 0;
        for (int k = 1; k <= MAXK; k++) {
            int n2 = 2 * k * G;
            if (n2 >= minN && n2 <= MAXN) fk[nf++] = k;
        }
        if (nf == 0) break;
        int lim = nf < 3 ? nf : 3;
        K_ = fk[rndi(lim)];
        int N = 2 * K_ * G;
        alloc_state(N);
        double remain = tend - now();
        double s = slice < remain ? slice : remain;
        if (s <= 0) break;
        int ok = search(now() + s, 30000, 4000, 8);
        if (ok) {
            if (N > bestN) store_best(N);
            minN = N + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestEc);
    for (int p = 0; p < bestEc; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
    return 0;
}
'''


# ------------------------------------------------------------ group tables

def _table(elems, mul):
    """Flat multiplication table: tab[x*G + y] = index of elems[x]*elems[y]. elems[0] must be the identity."""
    idx = {e: i for i, e in enumerate(elems)}
    G = len(elems)
    tab = [0] * (G * G)
    for x, a in enumerate(elems):
        base = x * G
        for y, b in enumerate(elems):
            tab[base + y] = idx[mul(a, b)]
    return G, tab


def _odd_perm(p):
    inv = 0
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                inv += 1
    return inv % 2 == 1


def _perm_group(n, even):
    elems = [p for p in itertools.permutations(range(n)) if not (even and _odd_perm(p))]
    mul = lambda a, b: tuple(a[b[i]] for i in range(n))
    return _table(elems, mul)


def _mat_group(p, kind):
    """kind: 'SL' (det 1), 'PSL' (SL modulo +-1), 'PGL' (GL modulo scalars)."""
    def det(m):
        return (m[0] * m[3] - m[1] * m[2]) % p

    def canon(m):
        if kind == "PSL":
            neg = tuple((-x) % p for x in m)
            return min(m, neg)
        if kind == "PGL":
            for x in m:
                if x:
                    inv = pow(x, p - 2, p)
                    return tuple(y * inv % p for y in m)
        return m

    if kind == "PGL":
        cand = [m for m in itertools.product(range(p), repeat=4) if det(m)]
    else:
        cand = [m for m in itertools.product(range(p), repeat=4) if det(m) == 1]
    ident = canon((1, 0, 0, 1))
    els = {canon(m) for m in cand}
    els.discard(ident)
    elems = [ident] + sorted(els)

    def mul(a, b):
        return canon((
            (a[0] * b[0] + a[1] * b[2]) % p, (a[0] * b[1] + a[1] * b[3]) % p,
            (a[2] * b[0] + a[3] * b[2]) % p, (a[2] * b[1] + a[3] * b[3]) % p,
        ))
    return _table(elems, mul)


def _heis(p):
    """Heisenberg group of order p^3."""
    elems = list(itertools.product(range(p), repeat=3))
    mul = lambda a, b: ((a[0] + b[0]) % p, (a[1] + b[1]) % p,
                        (a[2] + b[2] + a[0] * b[1]) % p)
    return _table(elems, mul)


def _agl(p):
    """Affine group AGL(1,p) of order p(p-1)."""
    elems = [(0, 1)] + [(a, u) for u in range(1, p) for a in range(p) if (a, u) != (0, 1)]
    mul = lambda x, y: ((x[0] + x[1] * y[0]) % p, (x[1] * y[1]) % p)
    return _table(elems, mul)


# (name, order, builder). Mostly non-metacyclic groups, which the earlier search never used.
_GROUPS = [
    ("H7", 343, lambda: _heis(7)),
    ("SL25", 120, lambda: _mat_group(5, "SL")),
    ("S5", 120, lambda: _perm_group(5, False)),
    ("A5", 60, lambda: _perm_group(5, True)),
    ("PSL27", 168, lambda: _mat_group(7, "PSL")),
    ("PGL27", 336, lambda: _mat_group(7, "PGL")),
    ("SL27", 336, lambda: _mat_group(7, "SL")),
    ("H5", 125, lambda: _heis(5)),
    ("AGL19", 342, lambda: _agl(19)),
    ("A6", 360, lambda: _perm_group(6, True)),
    ("AGL23", 506, lambda: _agl(23)),
    ("PSL211", 660, lambda: _mat_group(11, "PSL")),
    ("S6", 720, lambda: _perm_group(6, False)),
    ("AGL17", 272, lambda: _agl(17)),
    ("AGL13", 156, lambda: _agl(13)),
    ("AGL11", 110, lambda: _agl(11)),
]

_MAX_K = 8
_MAX_N = 4000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if d < 3 or d > 16 or D < 3:
        return best

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget

    todo = [g for g in _GROUPS if _MAX_K * 2 * g[1] >= best_n + 1 and 2 * g[1] <= _MAX_N]
    for idx, (name, order, make) in enumerate(todo):
        left = len(todo) - idx
        if deadline - time.monotonic() < 2.0:
            break
        try:
            G, tab = make()
        except Exception:
            continue
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        slice_s = remaining / left
        try:
            edges = [(p // G, tab[p]) for p in range(G * G)]
            out = lib.run_c(C_SOURCE, [d, D, seed, round(slice_s, 2), best_n + 1],
                            stdin_graph=(G, edges), timeout=slice_s + 5.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

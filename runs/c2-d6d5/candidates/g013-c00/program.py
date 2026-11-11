import math
import random
import time

import numpy as np

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
#define GMAX 800

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

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;   /* MT[x*G+y] = x*y ; RS[s*G+y] = y*s^{-1} */
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];

/* Reads group from stdin: header "G m" with m = G*G, then m lines "x z" where
   p = x*G + y is the index and z = x*y. */
static int read_group(void) {
    int G = 0, m = 0;
    if (scanf("%d %d", &G, &m) != 2) return 0;
    if (G < 1 || G > GMAX || m != G * G) return 0;
    int *mt = malloc(sizeof(int) * (size_t)m);
    int *rsv = malloc(sizeof(int) * (size_t)m);
    int *mark = malloc(sizeof(int) * (size_t)G);
    int ok = (mt != NULL && rsv != NULL && mark != NULL);
    for (int p = 0; ok && p < m; p++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) ok = 0;
        else if (a != p / G || b < 0 || b >= G) ok = 0;
        else mt[p] = b;
    }
    for (int s = 0; ok && s < G; s++) {
        memset(mark, 0, sizeof(int) * (size_t)G);
        for (int g = 0; ok && g < G; g++) {
            int y = mt[g * G + s];
            if (mark[y]) ok = 0;
            else mark[y] = 1;
        }
    }
    if (!ok) {
        free(mt); free(rsv); free(mark);
        return 0;
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            rsv[s * G + mt[g * G + s]] = g;
    free(MT); free(RS);
    MT = mt; RS = rsv; G_ = G;
    free(mark);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,x} ~ B_{j, x*s}. Vertices: A_{i,x} = i*G+x, B_{j,y} = (K+j)*G+y. */
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

/* Cost = unreached (block representative, vertex) pairs + heavy penalty for duplicate darts.
   Left translation is transitive on each block, so block representatives suffice. */
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

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    double tl = atof(argv[4]);
    double tend = now() + tl;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    K_ = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 3 || K_ < 1 || K_ > MAXK || 2 * K_ > 60) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (!read_group()) { printf("0 0\n"); return 0; }
    alloc_state(2 * K_ * G_);

    int ok = 0;
    while (!ok && now() < tend) {
        ok = search(tend, 20000, 3000, 6);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    int kG = K_ * G_;
    printf("%d %d\n", N_, kG * d_);
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", u, nb[(size_t)l * N_ + u]);
    return 0;
}
'''


MAXK = 8
GMAX = 800
TARGET_FRACTION = 0.44   # aim above this fraction of the Moore bound
MAX_TASKS = 14


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _prime_factors(n):
    f = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            f.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        f.append(n)
    return f


def _prim_root(p):
    fs = _prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    return 1


def _psl_gens(p, full):
    """Generators of PSL(2,p) (or PGL(2,p)) acting on the p+1 points of the projective line (p = infinity)."""
    inf = p

    def mob(f):
        return tuple(f(x) for x in range(p + 1))

    def s(x):
        if x == inf:
            return 0
        if x == 0:
            return inf
        return (-pow(x, p - 2, p)) % p

    gens = [mob(lambda x: (x + 1) % p if x < p else inf), mob(s)]
    if full:
        g = _prim_root(p)
        gens.append(mob(lambda x: (g * x) % p if x < p else inf))
    return gens


def _agl_gens(p):
    """Generators of AGL(1,p) acting on Z_p."""
    g = _prim_root(p)
    return [tuple((x + 1) % p for x in range(p)), tuple((g * x) % p for x in range(p))]


def _sym_gens(n):
    swap = tuple([1, 0] + list(range(2, n)))
    cyc = tuple((i + 1) % n for i in range(n))
    return [swap, cyc]


def _alt_gens(n):
    three = tuple([1, 2, 0] + list(range(3, n)))
    if n % 2 == 1:
        big = tuple((i + 1) % n for i in range(n))
    else:
        big = tuple([0] + [1 + (i % (n - 1)) for i in range(1, n)])
    return [three, big]


def _dprod(gA, nA, gB, nB):
    """Generators of the direct product acting on disjoint supports."""
    out = [tuple(list(g) + list(range(nA, nA + nB))) for g in gA]
    out += [tuple(list(range(nA)) + [nA + x for x in g]) for g in gB]
    return out


def _perm_table(gens):
    """Closure of permutation generators; returns (G, flat table) with table[x*G+y] = index of x∘y, or None if too big."""
    gens = [tuple(g) for g in gens]
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(x[j] for j in g)
            if y not in index:
                if len(elems) >= GMAX:
                    return None
                index[y] = len(elems)
                elems.append(y)
    G = len(elems)
    E = np.array(elems, dtype=np.int64)
    w = np.array([n ** j for j in range(n)], dtype=np.int64)
    keyidx = {k: i for i, k in enumerate((E @ w).tolist())}
    table = np.empty((G, G), dtype=np.int64)
    for x in range(G):
        keys = (E[x][E] @ w).tolist()
        table[x] = [keyidx[k] for k in keys]
    return G, table.reshape(-1).tolist()


def _sd(m, k2, r):
    order, mul, _ = lib.semidirect_group(m, k2, r)
    if order > GMAX:
        return None
    return order, [mul(x, y) for x in range(order) for y in range(order)]


def _semidirect_samples(rng, count):
    found = []
    tries = 0
    while len(found) < count and tries < 3000:
        tries += 1
        m = rng.randint(3, 40)
        k2 = rng.randint(2, 24)
        if not (90 <= m * k2 <= 420):
            continue
        r = rng.randint(2, m - 1)
        if math.gcd(r, m) != 1 or pow(r, k2, m) != 1 % m:
            continue
        if (m, k2, r) not in found:
            found.append((m, k2, r))
    return found


def _specs(rng):
    """name -> (estimated order, maker returning (G, flat table) or None)."""
    specs = {}

    def put(name, est, mk):
        specs[name] = (est, mk)

    for p in (5, 7, 11):
        put(f"PSL2({p})", p * (p * p - 1) // 2, lambda p=p: _perm_table(_psl_gens(p, False)))
        put(f"PGL2({p})", p * (p * p - 1), lambda p=p: _perm_table(_psl_gens(p, True)))
    for p in (11, 13, 17, 19):
        put(f"AGL1({p})", p * (p - 1), lambda p=p: _perm_table(_agl_gens(p)))
    for n in (5, 6):
        put(f"S{n}", math.factorial(n), lambda n=n: _perm_table(_sym_gens(n)))
        put(f"A{n}", math.factorial(n) // 2, lambda n=n: _perm_table(_alt_gens(n)))
    put("PSL2(7)xC2", 336, lambda: _perm_table(_dprod(_psl_gens(7, False), 8, [(1, 0)], 2)))
    put("PSL2(7)xC3", 504, lambda: _perm_table(_dprod(_psl_gens(7, False), 8, [(1, 2, 0)], 3)))
    put("A5xC2", 120, lambda: _perm_table(_dprod(_alt_gens(5), 5, [(1, 0)], 2)))
    put("A5xC3", 180, lambda: _perm_table(_dprod(_alt_gens(5), 5, [(1, 2, 0)], 3)))
    put("PGL2(5)xC3", 360, lambda: _perm_table(_dprod(_psl_gens(5, True), 6, [(1, 2, 0)], 3)))
    put("S5xC2", 240, lambda: _perm_table(_dprod(_sym_gens(5), 5, [(1, 0)], 2)))

    for m, k2, r in _semidirect_samples(rng, 4):
        put(f"SD({m},{k2},{r})", m * k2, lambda m=m, k2=k2, r=r: _sd(m, k2, r))
    return specs


def _plan(T, moore, specs):
    tasks = []
    for name, (est, _) in specs.items():
        count = 0
        for k in range(1, MAXK + 1):
            N = 2 * k * est
            if N > moore:
                break
            if N >= T:
                tasks.append((N, name, k))
                count += 1
                if count == 2:
                    break
    tasks.sort()
    return tasks[:MAX_TASKS]


def build(d, D, seed, time_limit):
    t0 = time.time()
    hard_end = t0 + max(1.0, time_limit - 4.0)
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

    # New family: bi-Cayley lifts over explicit group tables, including
    # non-solvable permutation groups (PSL/PGL(2,p), A_n, S_n), their direct
    # products with small cyclic groups, affine groups and random semidirect products.
    moore = lib.moore_bound(d, D)
    T = max(best_n + 1, int(TARGET_FRACTION * moore) + 1)
    rng = random.Random(seed * 1000003 + d * 101 + D)
    specs = _specs(rng)
    tasks = _plan(T, moore, specs)

    cache = {}
    for idx, (_, name, k) in enumerate(tasks):
        if hard_end - time.time() < 1.0:
            break
        if name not in cache:
            try:
                res = specs[name][1]()
                if res is None:
                    cache[name] = None
                else:
                    G, table = res
                    cache[name] = (G, [(p // G, table[p]) for p in range(G * G)])
            except Exception:
                cache[name] = None
        grp = cache[name]
        if grp is None:
            continue
        G, edges = grp
        if not (T <= 2 * k * G <= moore):
            continue

        now = time.time()
        share = (hard_end - now) / max(1, len(tasks) - idx)
        budget = min(max(share, 1.0), hard_end - now)
        if budget < 0.8:
            break
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 131 + idx, round(budget - 0.5, 2), k],
                            stdin_graph=(G, edges), timeout=budget + 1.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

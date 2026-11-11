"""Generic-group two-orbit voltage lifts for the bipartite degree-diameter problem.

Change in this version: the C engine no longer searches only over affine groups
F_q x| H. Python now proposes several group families (affine Z_p x| C_c for prime p,
semidirect products Z_m x| Z_k, and direct products), and C builds the multiplication
table from a compact parameter description. The lift has K left and K right orbits
(K = 2 gives 4|G| vertices, K = 1 gives 2|G| vertices). The voltage search is
simulated annealing over dart targets and voltages. Python searches over group
orders with binary search followed by a short upward climb. Every returned graph is
checked with lib.is_valid, and K_{d,d} is kept as the fallback.
"""
import math
import random
import time

import lib

MAXN = 2600

C_SOURCE = r'''
/* Voltage-lift search over an arbitrary finite group given by a formula.
 * Usage: prog d D seed time_limit K TYPE P1 P2 P3
 *   TYPE 0: semidirect Z_P1 x| Z_P2 with r = P3 (r = 1 gives a direct product).
 *           element (a,b) coded a*P2+b, product (a,b)(c,e) = (a + r^b c, b+e).
 *   TYPE 1: Z_P1 x| C_P2 (P1 prime, P2 | P1-1, P3 a primitive root mod P1).
 *           element (a,j) coded a*P2+j, product (a,j)(b,t) = (a + h_j b, j+t),
 *           with h_j = P3^(j*(P1-1)/P2).
 * Vertices: left L^a_x = a*N+x (a < K), right R^b_y = K*N + b*N + y.
 * Output: "n m" then m edge lines for the first valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2600
#define MAXD 32
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)

static int N, K, d, D, nd;
static int TYPE, MM, KK, PP, CC;
static int PW[MAXN], HV[MAXN];
static int *MT;
static int INV[MAXN];
static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN];
static int invT[MAXND][MAXN];
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int gmul(int x, int y) {
    if (TYPE == 0) {
        int a = x / KK, b = x % KK, c = y / KK, e = y % KK;
        int na = (int)(((long long)a + (long long)PW[b] * c) % MM);
        int nb = (b + e) % KK;
        return na * KK + nb;
    }
    int a = x / CC, j = x % CC, b = y / CC, t = y % CC;
    int na = (int)(((long long)a + (long long)HV[j] * b) % PP);
    int nj = (j + t) % CC;
    return na * CC + nj;
}

static int build_table(void) {
    MT = malloc(sizeof(int) * (size_t)N * (size_t)N);
    if (!MT) return 0;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gmul(x, y);
    for (int x = 0; x < N; x++)
        if (MT[x] != x || MT[x * N] != x) return 0; /* identity is 0 */
    for (int x = 0; x < N; x++) INV[x] = -1;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) INV[x] = y;
    for (int x = 0; x < N; x++)
        if (INV[x] < 0) return 0;
    return 1;
}

/* Dart t leaves left orbit t/d: L^a_x ~ R^{tb[t]}_{x * g}, g = vg[t]. */
static void set_dart(int t, int g) {
    vg[t] = g;
    int ig = INV[g];
    for (int x = 0; x < N; x++) {
        fwdT[t][x] = MT[x * N + g];
        invT[t][x] = MT[x * N + ig];
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

static void random_init(void) {
    int list[MAXND];
    int p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i];
        list[i] = list[j];
        list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(N));
}

static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

static int bfs_count(int src) {
    int V2 = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / N, x = v % N;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * N + fwdT[t][x];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int w = v - V2;
                int b = w / N, y = w % N;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * N + invT[t][y];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Left translations act transitively on each orbit, so one BFS per orbit
 * (2K in total) decides the diameter. */
static long cover_cost(void) {
    long V = 2L * K * N;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_count(a * N);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * N + b * N);
    return c + 1000L * dup_count();
}

static int anneal(void) {
    const int iters = 4000;
    while (now() < t_end) {
        random_init();
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > t_end) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1];
                tb[t1] = tb[t2];
                tb[t2] = tmp;
                rebuild_inc();
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1];
                    tb[t1] = tb[t2];
                    tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd);
                int g = rndint(N);
                if (g == vg[t]) continue;
                int old = vg[t];
                set_dart(t, g);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

static void print_result(void) {
    int V = 2 * K * N;
    printf("%d %d\n", V, K * N * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * N + tb[t] * N + fwdT[t][x];
                printf("%d %d\n", a * N + x, u);
            }
}

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    TYPE = atoi(argv[6]);
    int P1 = atoi(argv[7]), P2 = atoi(argv[8]), P3 = atoi(argv[9]);
    if (d < 2 || d > MAXD || D < 3 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    nd = K * d;

    if (TYPE == 0) {
        MM = P1;
        KK = P2;
        if (MM < 1 || KK < 1) { printf("0 0\n"); return 0; }
        long long nn = (long long)MM * KK;
        if (nn < 2 || nn > MAXN) { printf("0 0\n"); return 0; }
        N = (int)nn;
        PW[0] = 1 % MM;
        for (int b = 1; b < KK; b++)
            PW[b] = (int)((long long)PW[b - 1] * P3 % MM);
        if ((long long)PW[KK - 1] * P3 % MM != 1 % MM) { printf("0 0\n"); return 0; }
    } else {
        PP = P1;
        CC = P2;
        if (PP < 3 || CC < 1) { printf("0 0\n"); return 0; }
        long long nn = (long long)PP * CC;
        if (nn < 2 || nn > MAXN || (PP - 1) % CC != 0) { printf("0 0\n"); return 0; }
        N = (int)nn;
        long long step = (PP - 1) / CC;
        for (int j = 0; j < CC; j++)
            HV[j] = (int)powmod(P3, (long long)j * step, PP);
        if (HV[0] != 1) { printf("0 0\n"); return 0; }
    }

    if (!build_table()) {
        printf("0 0\n");
        return 0;
    }

    t_end = now() + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (!anneal()) {
        printf("0 0\n");
        return 0;
    }
    print_result();
    return 0;
}
'''


def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _prim_root(p):
    """Smallest primitive root modulo the prime p."""
    n = p - 1
    fs = []
    f = 2
    while f * f <= n:
        if n % f == 0:
            fs.append(f)
            while n % f == 0:
                n //= f
        f += 1
    if n > 1:
        fs.append(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    return None


def _structures(N, seed):
    """Group descriptions of order N, most promising first.

    Entries are ('aff', p, c, g) for Z_p x| C_c, or ('sd', m, k, r) for
    Z_m x| Z_k (r = 1 is a direct product)."""
    rng = random.Random(seed * 1000003 + N * 7 + 1)
    aff, sd, dp = [], [], []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if math.gcd(m, k) > 1:
            dp.append(('sd', m, k, 1))
        target = 1 % m
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == target:
                sd.append(('sd', m, k, r))
    for p in range(3, N + 1):
        if N % p or not _is_prime(p):
            continue
        c = N // p
        if c >= 2 and (p - 1) % c == 0:
            g = _prim_root(p)
            if g is not None:
                aff.append(('aff', p, c, g))
    rng.shuffle(aff)
    rng.shuffle(sd)
    pool = aff + sd
    if pool:
        return pool[:3]
    if dp:
        return dp[:2] + [('sd', N, 1, 1)]
    return [('sd', N, 1, 1)]


def _probe(N, d, D, seed, budget, K, tries=3):
    """Try a few groups of order N with K orbits. Returns (n, edges) or None."""
    if N > MAXN or budget < 0.5:
        return None
    structs = _structures(N, seed)[:tries]
    if not structs:
        return None
    share = budget / len(structs)
    for s in structs:
        if s[0] == 'aff':
            gp = [1, s[1], s[2], s[3]]
        else:
            gp = [0, s[1], s[2], s[3]]
        text = lib.run_c(C_SOURCE, [d, D, seed, round(share, 2), K] + gp,
                         stdin_graph=None, timeout=share + 10.0)
        n, e = lib.parse_graph_text(text)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    return None


def _search(d, D, seed, lo, hi, K, end):
    """Binary search over the group order N in [lo, hi], then a short climb.

    Returns the valid graph with the largest group order found, or None."""
    if lo > hi:
        return None
    Ns = list(range(lo, hi + 1))
    best = None
    bestN = None
    li, hi_i = 0, len(Ns) - 1
    while li <= hi_i:
        rem = end - time.monotonic()
        if rem < 3.0:
            break
        mid = (li + hi_i) // 2
        res = _probe(Ns[mid], d, D, seed, max(1.5, 0.2 * rem), K)
        if res is not None:
            best = res
            bestN = Ns[mid]
            li = mid + 1
        else:
            hi_i = mid - 1
    if bestN is None:
        return best
    fails = 0
    cur = bestN + 1
    while fails < 2 and cur <= hi:
        rem = end - time.monotonic()
        if rem < 3.0:
            break
        res = _probe(cur, d, D, seed, max(1.5, 0.25 * rem), K)
        if res is not None:
            best = res
            bestN = cur
            fails = 0
        else:
            fails += 1
        cur += 1
    return best


# ------------------------------------------------- algebraic small-case helpers

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    import itertools
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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    seed = int(seed)
    hard = t0 + time_limit - max(4.0, 0.08 * time_limit)

    def room():
        return hard - time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if D >= 3 and d >= 3:
        mb = lib.moore_bound(d, D)

        # Stage A: two left and two right orbits, 4N vertices, generic groups.
        end = time.monotonic() + 0.55 * room()
        if end - time.monotonic() > 5.0:
            lo = max(best[0] // 4 + 1, 2)
            hi = min(mb // 4, MAXN)
            try:
                consider(_search(d, D, seed, lo, hi, 2, end))
            except Exception:
                pass

        # Stage B: one orbit each side (2N vertices), with the remaining time.
        if room() > 5.0:
            lo = max(best[0] // 2 + 1, 2)
            hi = min(mb // 2, MAXN)
            try:
                consider(_search(d, D, seed + 1, lo, hi, 1, hard))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

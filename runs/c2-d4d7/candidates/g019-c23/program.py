"""Bi-Cayley search over non-abelian groups for the weakest target (d=4, D=7).

Change from the parent: the voltage-lift search is replaced by a different construction. Each graph is
the bipartite double of a Cayley graph: vertices A(x) and B(x) for x in a group G of order N, with
edges A(x)-B(x*s) for d distinct generators s. Left multiplication is an automorphism, so
diameter <= D holds iff BFS from A(e) and B(e) reaches everything within D. The C search uses
simulated annealing over generator tuples on many groups: explicit PSL(2,p)/PGL(2,p) times Z_k, and
semidirect products Z_m x| Z_k. The window of orders is just above the current best. Every
result is re-checked by an all-sources BFS in C and by lib.is_valid in Python. If anything fails,
the best valid graph so far is returned, and the start graph is the fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1100
#define MAXD 16
#define MAXV (2 * MAXG)
#define HS 8192
#define NTYPES 7

static int d, D;
static double t_end;

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

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
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

/* ---------------------------------------------------------- permutation groups */
typedef struct { unsigned char p[16]; } Perm;
static Perm EL[MAXG];
static uint64_t hk[HS];
static int hv[HS];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}
static unsigned hslot(uint64_t k) { return (unsigned)((k * 0x9E3779B97F4A7C15ULL) >> 51); }
static int hfind(uint64_t k) {
    unsigned h = hslot(k);
    while (hv[h]) {
        if (hk[h] == k) return hv[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}
static void hput(uint64_t k, int idx) {
    unsigned h = hslot(k);
    while (hv[h]) h = (h + 1) & (HS - 1);
    hk[h] = k;
    hv[h] = idx + 1;
}

/* Closure of <x+1, -1/x> (PSL(2,p)) or with x -> prim*x added (PGL(2,p)) on P^1(F_p).
 * Returns the group order, or 0 on overflow. Identity is EL[0]. */
static int perm_closure(int p, int pgl) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    unsigned char gen[3][16];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x <= p; x++)
        gen[0][x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[1][x] = (unsigned char)v;
    }
    ng = 2;
    if (pgl) {
        for (int x = 0; x <= p; x++)
            gen[2][x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
        ng = 3;
    }
    memset(hv, 0, sizeof hv);
    memset(&EL[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) EL[0].p[x] = (unsigned char)x;
    hput(pkey(EL[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[qi].p[gen[k][x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXG) return 0;
                EL[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    return n;
}

static const int BP[NTYPES] = {3, 3, 5, 5, 7, 7, 11};
static const int BG[NTYPES] = {0, 1, 0, 1, 0, 1, 0};
static int *btab[NTYPES];
static int bord[NTYPES];

static void init_bases(void) {
    for (int b = 0; b < NTYPES; b++) {
        btab[b] = NULL;
        bord[b] = 0;
        int o = perm_closure(BP[b], BG[b]);
        if (!o) continue;
        int s = BP[b] + 1;
        int *t = malloc(sizeof(int) * (size_t)o * (size_t)o);
        if (!t) continue;
        for (int i = 0; i < o; i++)
            for (int j = 0; j < o; j++) {
                Perm h;
                memset(&h, 0, sizeof h);
                for (int x = 0; x < s; x++) h.p[x] = EL[i].p[EL[j].p[x]];
                int idx = hfind(pkey(h.p, s));
                t[i * o + j] = idx < 0 ? 0 : idx;
            }
        btab[b] = t;
        bord[b] = o;
    }
}

/* ---------------------------------------------------------------- current group */
static int GN;
static int GT[MAXG * MAXG];
static int INV[MAXG];

static void set_prod(int b, int k) {
    int o = bord[b], N = o * k;
    GN = N;
    const int *bt = btab[b];
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] = bt[x * o + y] * k + (c + e) % k;
}

static void set_semi(int m, int k, int r) {
    int N = m * k;
    GN = N;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)((((long)a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
}

static void compute_inv(void) {
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (GT[x * GN + y] == 0) { INV[x] = y; break; }
}

/* Pick a group of order in [lo, hi]: a direct product of a base group with Z_k (preferred),
 * or a random semidirect product Z_m x| Z_k. */
static int choose_group(int lo, int hi) {
    int cb[64], ck[64], cnt = 0;
    for (int b = 0; b < NTYPES; b++) {
        if (!bord[b]) continue;
        int o = bord[b];
        for (int k = 1; o * k <= hi; k++) {
            int N = o * k;
            if (N >= lo && N <= hi && cnt < 64) { cb[cnt] = b; ck[cnt] = k; cnt++; }
        }
    }
    if (cnt > 0 && rndint(10) < 6) {
        int c = rndint(cnt);
        set_prod(cb[c], ck[c]);
        return 1;
    }
    if (hi < lo) return 0;
    int N = lo + rndint(hi - lo + 1);
    int bm = 0, bk = 0, br = 0;
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    set_semi(bm, bk, br);
    return 1;
}

/* ---------------------------------------------------------------- bi-Cayley core */
static int SG[MAXD];
static int dist[MAXV], que[MAXV];

/* BFS in the bi-Cayley graph: A(x) ~ B(x*s), indices A = x, B = N + y. */
static void bfs(int src) {
    int N = GN, nv = 2 * N;
    for (int i = 0; i < nv; i++) dist[i] = -1;
    int h = 0, t = 0;
    dist[src] = 0;
    que[t++] = src;
    while (h < t) {
        int u = que[h++];
        int du = dist[u] + 1;
        if (u < N) {
            int base = u * N;
            for (int s = 0; s < d; s++) {
                int v = N + GT[base + SG[s]];
                if (dist[v] < 0) { dist[v] = du; que[t++] = v; }
            }
        } else {
            int base = (u - N) * N;
            for (int s = 0; s < d; s++) {
                int v = GT[base + INV[SG[s]]];
                if (dist[v] < 0) { dist[v] = du; que[t++] = v; }
            }
        }
    }
}

/* Excess distance from the two sources A(e) and B(e); zero iff diameter <= D. */
static long cost(void) {
    long c = 0;
    int N = GN;
    int srcs[2] = {0, N};
    for (int q = 0; q < 2; q++) {
        bfs(srcs[q]);
        for (int i = 0; i < 2 * N; i++) {
            if (dist[i] < 0) c += 2;
            else if (dist[i] > D) c += dist[i] - D;
        }
    }
    return c;
}

static int full_ok(void) {
    int N = GN, nv = 2 * N;
    for (int src = 0; src < nv; src++) {
        bfs(src);
        for (int i = 0; i < nv; i++)
            if (dist[i] < 0 || dist[i] > D) return 0;
    }
    return 1;
}

static int best_n = 0, best_m = 0;
static int bu[MAXG * MAXD], bv[MAXG * MAXD];

static void store(void) {
    int N = GN;
    best_n = 2 * N;
    best_m = 0;
    for (int x = 0; x < N; x++)
        for (int s = 0; s < d; s++) {
            bu[best_m] = x;
            bv[best_m] = N + GT[x * N + SG[s]];
            best_m++;
        }
}

/* Simulated annealing over d distinct generators of the current group. */
static int sa_run(int steps, double until) {
    int N = GN;
    if (N < d) return 0;
    for (int i = 0; i < d; i++) {
        int g, ok;
        do {
            g = rndint(N);
            ok = 1;
            for (int j = 0; j < i; j++) if (SG[j] == g) ok = 0;
        } while (!ok);
        SG[i] = g;
    }
    long cur = cost();
    double T = 1.5;
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int i = rndint(d), g = rndint(N), dup = 0;
        for (int j = 0; j < d; j++) if (SG[j] == g) { dup = 1; break; }
        if (dup) continue;
        int old = SG[i];
        SG[i] = g;
        long nv = cost();
        long delta = nv - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nv;
        else SG[i] = old;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.88;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int ch;
    while ((ch = getchar()) != EOF) { }

    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    init_bases();
    long moore = moore_bound();
    long hi_all = moore / 2;
    if (hi_all > MAXG) hi_all = MAXG;

    while (now() < t_end) {
        int lo = best_n / 2 + 1;
        if (lo < d + 1) lo = d + 1;
        int hi = (int)hi_all;
        if (lo + 250 < hi) hi = lo + 250;
        if (lo > hi) break;
        if (!choose_group(lo, hi)) continue;
        if (GN < d) continue;
        compute_inv();
        if (sa_run(20000, t_end)) {
            if (2 * GN > best_n && full_ok()) store();
        }
    }

    if (best_n > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++) printf("%d %d\n", bu[i], bv[i]);
    } else {
        printf("0 0\n");
    }
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Several sign conventions are tried; a candidate is kept only if lib.is_valid accepts it.
    Returns None if nothing verifies.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    try:
        for n, e in known_starts(d, D):
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    except Exception:
        pass

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=None, timeout=budget + 5.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best

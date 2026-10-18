"""Bi-Cayley search over non-metacyclic groups for the weakest target (d=4, D=7).

Change from the parent: the lift-and-grow pipeline is replaced by one bi-Cayley search. A bipartite
graph on A = G and B = G is built from a group G of order N and a connection set S of d distinct
elements, with A_x adjacent to B_{xs} for s in S. Left multiplication is an automorphism, so the
diameter test needs only two BFS runs (from A_e and B_e), each costing O(N d). That makes the
objective cheap enough for simulated annealing over S in each group.

Groups: cyclic Z_N, semidirect Z_m x| Z_k, and direct products of PSL(2,p) or PGL(2,p) (p = 5, 7, 11)
with Z_k. Target orders N run up to the Moore bound (1093 for d=4, D=7), so vertex counts reach 2N.
Every candidate is re-checked by a full all-sources BFS before it is accepted. The Python side keeps
the best known start graph (GH(3,3) incidence, or K_{d,d}) and returns it unless a larger valid graph
is verified.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Graph: vertices A_x = x and B_y = N + y for x, y in G, |G| = N. Edge A_x -- B_{x s} for s in S,
 * |S| = d. Left multiplication is an automorphism, so the graph has diameter <= D iff the BFS from
 * A_e and from B_e both reach everything within D steps. Simulated annealing over S uses the
 * number of bad vertices from those two sources as the energy.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1200
#define MAXV (2 * MAXG)
#define MAXD 32
#define MAXE 40000
#define NBASE 5
#define HS 8192
#define PMAX 700

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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

/* ---------------------------------------------------------------- group tables */
static int N;                 /* current group order */
static int GT[MAXG * MAXG];   /* GT[x*N+y] = x*y, identity 0 */
static int GI[MAXG];          /* inverses */
static int rp[MAXG];

static int *BT[NBASE];
static int BO[NBASE];

typedef struct { unsigned char p[16]; } Perm;
static Perm ELEM[PMAX];
static uint64_t hkey[HS];
static int hval[HS];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
}

static int hfind(uint64_t key) {
    unsigned h = hslot(key);
    while (hval[h]) {
        if (hkey[h] == key) return hval[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(uint64_t key, int idx) {
    unsigned h = hslot(key);
    while (hval[h]) h = (h + 1) & (HS - 1);
    hkey[h] = key;
    hval[h] = idx + 1;
}

/* Multiplication table of PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) acting on P^1(F_p). */
static int *make_base(int p, int pgl, int *ordp) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x <= p; x++)
        gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
    ng++;
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[ng].p[x] = (unsigned char)v;
    }
    ng++;
    if (pgl) {
        for (int x = 0; x <= p; x++)
            gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
        ng++;
    }

    memset(hval, 0, sizeof hval);
    memset(ELEM, 0, sizeof ELEM);
    for (int x = 0; x < s; x++) ELEM[0].p[x] = (unsigned char)x;
    hput(pkey(ELEM[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= PMAX) return NULL;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    int *tab = malloc(sizeof(int) * (size_t)n * (size_t)n);
    if (!tab) return NULL;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * n + j] = idx < 0 ? 0 : idx;
        }
    *ordp = n;
    return tab;
}

static void init_bases(void) {
    static const int BP[NBASE] = {5, 5, 7, 7, 11};
    static const int BG[NBASE] = {0, 1, 0, 1, 0};
    for (int b = 0; b < NBASE; b++) {
        BO[b] = 0;
        BT[b] = make_base(BP[b], BG[b], &BO[b]);
        if (!BT[b]) BO[b] = 0;
    }
}

static void set_cyclic(int M) {
    N = M;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            GT[x * N + y] = (x + y) % N;
}

/* Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static void set_semidirect(int m, int k, int r) {
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
}

/* Base group b times Z_k: element x*k+c. */
static void set_product(int b, int k) {
    int o = BO[b];
    N = o * k;
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++) {
            int X = x * k + c;
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[X * N + (y * k + e)] = BT[b][x * o + y] * k + (c + e) % k;
        }
}

static int compute_inverses(void) {
    for (int x = 0; x < N; x++) {
        int found = -1;
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { found = y; break; }
        if (found < 0) return 0;
        GI[x] = found;
    }
    return 1;
}

/* Random group of order M: semidirect, product with a PSL/PGL base, or cyclic. */
static int make_group(int M) {
    int choice = rndint(10);
    if (choice >= 3 && choice < 6) {
        for (int att = 0; att < 80; att++) {
            int m = 2 + rndint(M - 1);
            if (M % m) continue;
            int k = M / m;
            if (k < 2) continue;
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            set_semidirect(m, k, r);
            return compute_inverses();
        }
    } else if (choice >= 6) {
        int cand[NBASE], nc = 0;
        for (int b = 0; b < NBASE; b++)
            if (BO[b] > 0 && M % BO[b] == 0) cand[nc++] = b;
        if (nc > 0) {
            int b = cand[rndint(nc)];
            set_product(b, M / BO[b]);
            return compute_inverses();
        }
    }
    set_cyclic(M);
    return compute_inverses();
}

/* ---------------------------------------------------------------- bi-Cayley state */
static int S[MAXD], Sinv[MAXD];
static int dist_[MAXV], que[MAXV];

static int in_prefix(int g, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == g) return 1;
    return 0;
}

static void random_S(void) {
    for (int i = 0; i < d; i++) {
        int g;
        do { g = rndint(N); } while (in_prefix(g, i));
        S[i] = g;
        Sinv[i] = GI[g];
    }
}

/* Number of vertices not reached from src within D steps. */
static int bfs_from(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    que[t++] = src;
    while (h < t) {
        int v = que[h++];
        if (dist_[v] >= D) continue;
        int nd = dist_[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + GT[v * N + S[i]];
                if (dist_[u] < 0) { dist_[u] = nd; que[t++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = GT[y * N + Sinv[i]];
                if (dist_[u] < 0) { dist_[u] = nd; que[t++] = u; }
            }
        }
    }
    return V - t;
}

static long pair_bad(void) {
    return (long)bfs_from(0) + (long)bfs_from(N);
}

static int verify_full(void) {
    for (int s = 0; s < 2 * N; s++)
        if (bfs_from(s) != 0) return 0;
    return 1;
}

/* Simulated annealing over S for the current group. Returns 1 if a valid S was found. */
static int anneal(double until, long stall_cap) {
    random_S();
    long cur = pair_bad();
    long best = cur;
    double T = 1.0;
    long stall = 0;
    for (long it = 0;; it++) {
        if (cur == 0) return 1;
        if ((it & 127) == 0 && now() > until) return 0;
        if (stall > stall_cap) return 0;
        int i = rndint(d);
        int g = rndint(N);
        if (in_prefix(g, d)) continue;
        int old = S[i], oldi = Sinv[i];
        S[i] = g;
        Sinv[i] = GI[g];
        long nb = pair_bad();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
        } else {
            S[i] = old;
            Sinv[i] = oldi;
        }
        if (cur < best) { best = cur; stall = 0; }
        else stall++;
        T *= 0.999;
        if (T < 0.02) T = 1.0;
    }
}

/* ---------------------------------------------------------------- best graph */
static int best_n = 0;
static int ne = 0;
static int eu[MAXE], ev[MAXE];

static void read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return;
        if (u < 0 || v < 0 || u >= n || v >= n) return;
        eu[e] = u;
        ev[e] = v;
    }
    best_n = n;
    ne = m;
}

static void make_complete(void) {
    best_n = 2 * d;
    ne = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            eu[ne] = a;
            ev[ne] = d + b;
            ne++;
        }
}

static void record_best(void) {
    best_n = 2 * N;
    ne = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            eu[ne] = x;
            ev[ne] = N + GT[x * N + S[i]];
            ne++;
        }
}

static long moore_half(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000L) break;
    }
    return s;
}

static void search(void) {
    init_bases();
    long half = moore_half();
    long lo = best_n / 2 + 1;
    long hi = half < MAXG - 1 ? half : MAXG - 1;
    if (lo < d) lo = d;
    while (now() < t_end && lo <= hi) {
        int M = (int)(lo + rndint((int)(hi - lo + 1)));
        if (!make_group(M)) continue;
        double until = now() + 3.0;
        if (until > t_end) until = t_end;
        if (anneal(until, 40000L) && verify_full()) {
            record_best();
            lo = M + 1;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start();
    if (best_n == 0 && d >= 1 && d <= MAXD) make_complete();

    if (d >= 3 && d <= MAXD && D >= 2 && best_n > 0) search();

    printf("%d %d\n", best_n, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", eu[e], ev[e]);
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

    Returns None if no sign convention yields a graph that passes lib.is_valid with diameter 6.
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
    """Algebraic candidate graphs valid for diameter D (may be empty)."""
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3)],
                         stdin_graph=best, timeout=budget + 6)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best

"""Bold variant for the weak target (d=4, D=7): a different search regime, one C run.

Change from the parent: the C engine no longer hill-climbs lifts over fibres of size up to 4. It searches
small-base lifts (1 or 2 fibres per side, so bi-Cayley graphs and their 2-fibre cousins) over a much wider
group zoo: semidirect products Z_m x| Z_k (which include cyclic, direct-product and dihedral groups), and
PSL(2,p) / PGL(2,p) times Z_k for p = 5, 7, 11, 13. Groups are sampled freely from a window of orders just
above the current best, so the search ratchets upward. Each candidate is scored with a cheap orbit-reduced
BFS (only 2p fibre representatives, neighbours generated from the voltages on the fly) inside a simulated
annealing over voltages, with reheats. Any lift that reaches diameter D is re-checked by the full all-pairs
test before it is kept. The C engine receives the Python start order as an argument and prints "0 0" when it
finds nothing better, so the Python fallbacks (K_{d,d}, PG(2,q) incidence, W(q), H(3)) always remain valid.
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

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 1100
#define MAXP 2
#define MAXDART (MAXD * MAXP)
#define HS 8192
#define NB 6
#define SA_STEPS 15000
#define STALL_RESET 2500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

static int d, D;
static long moore;
static double t_end;
static Graph tmpg, bestg;
static int have_best = 0;
static long best_n;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (bitset BFS). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ---------------------------------------------------------------- groups
 * GT[x*GN+y] = x*y with identity 0. Every group acts regularly on itself by left
 * multiplication, which makes the orbit-reduced diameter test exact. */
static int GN;
static int *GT;
static int GT_store[MAXG * MAXG];
static int ginv[MAXG];
static int rp_tab[MAXG];

static int *base_tab[NB];
static int base_ord[NB];

typedef struct { unsigned char p[16]; } Perm;
static Perm ELEM[MAXG];
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

/* PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) as permutations of P^1(F_p). */
static int perm_closure(int p, int pgl, int *orderp) {
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
    memset(&ELEM[0], 0, sizeof(Perm));
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
                if (n >= MAXG) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *orderp = n;
    return 1;
}

static int *make_base_table(int p, int pgl, int *ordp) {
    int ord = 0;
    if (!perm_closure(p, pgl, &ord)) return NULL;
    int s = p + 1;
    int *tab = malloc(sizeof(int) * (size_t)ord * (size_t)ord);
    if (!tab) return NULL;
    for (int i = 0; i < ord; i++)
        for (int j = 0; j < ord; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * ord + j] = idx < 0 ? 0 : idx;
        }
    *ordp = ord;
    return tab;
}

static void init_bases(void) {
    static const int BP[NB] = {5, 5, 7, 7, 11, 13};
    static const int BG[NB] = {0, 1, 0, 1, 0, 0};
    for (int b = 0; b < NB; b++) {
        int ord = 0;
        base_tab[b] = make_base_table(BP[b], BG[b], &ord);
        base_ord[b] = base_tab[b] ? ord : 0;
    }
}

static void finish_group(void) {
    for (int x = 0; x < GN; x++) {
        ginv[x] = 0;
        for (int y = 0; y < GN; y++)
            if (GT[x * GN + y] == 0) { ginv[x] = y; break; }
    }
}

/* Direct product of base group b with Z_k: element x*k + c. */
static void set_product(int b, int k) {
    int o = base_ord[b], N = o * k;
    GN = N;
    GT = GT_store;
    const int *bt = base_tab[b];
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] = bt[x * o + y] * k + (c + e) % k;
    finish_group();
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_semidirect(int m, int k, int r) {
    int N = m * k;
    GN = N;
    GT = GT_store;
    rp_tab[0] = 1 % m;
    for (int b = 1; b < k; b++) rp_tab[b] = (int)((long)rp_tab[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)(((a + (long)rp_tab[b] * c) % m) * k + (b + e) % k);
        }
    }
    finish_group();
}

static int sample_semidirect(int N, int *mo, int *ko, int *ro) {
    int divs[64], nd_ = 0;
    for (int m = 1; m <= N && nd_ < 64; m++)
        if (N % m == 0) divs[nd_++] = m;
    for (int tries = 0; tries < 60; tries++) {
        int m = divs[rndint(nd_)];
        int k = N / m;
        if (m == 1) { *mo = 1; *ko = k; *ro = 0; return 1; }
        int r = 1 + rndint(m - 1);
        if (gcd(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        *mo = m; *ko = k; *ro = r;
        return 1;
    }
    return 0;
}

/* ---------------------------------------------------------------- lifts
 * Base: p fibres on each side, d*p darts. Dart (i,j,g) joins A_i element x to B_j element x*g. */
static Dart cdt[MAXDART];
static int cnd, cp, cN;
static Dart sa_best[MAXDART];
static int distb[MAXN], qbuf[MAXN];

static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int make_darts(int p, int N, Dart *dt) {
    int M[MAXP][MAXP];
    make_base(p, M);
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    return nd;
}

/* Orbit-reduced count of (fibre representative, vertex) pairs at distance > D. Zero iff diameter <= D. */
static long orbit_bad(void) {
    int p = cp, N = cN, nv = 2 * p * N;
    long total = 0;
    for (int a = 0; a < 2 * p; a++) {
        for (int v = 0; v < nv; v++) distb[v] = -1;
        int src = a * N, head = 0, tail = 0;
        distb[src] = 0;
        qbuf[tail++] = src;
        while (head < tail) {
            int v = qbuf[head++];
            if (distb[v] >= D) continue;
            int f = v / N, x = v - f * N;
            for (int t = 0; t < cnd; t++) {
                int w;
                if (f < p) {
                    if (cdt[t].i != f) continue;
                    w = (p + cdt[t].j) * N + GT[x * N + cdt[t].g];
                } else {
                    if (cdt[t].j != f - p) continue;
                    w = cdt[t].i * N + GT[x * N + ginv[cdt[t].g]];
                }
                if (distb[w] < 0) {
                    distb[w] = distb[v] + 1;
                    qbuf[tail++] = w;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Simulated annealing over the voltages for the current group. Returns 1 if diameter <= D. */
static int lift_sa(int p, int N, double until) {
    cp = p;
    cN = N;
    cnd = make_darts(p, N, cdt);
    long bad = orbit_bad();
    long best = bad;
    memcpy(sa_best, cdt, sizeof(Dart) * cnd);
    double T = 2.0;
    int stall = 0;
    for (long s = 0; s < SA_STEPS && best > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(cnd);
        int old = cdt[t].g;
        cdt[t].g = fresh_voltage(cdt, cnd, t, cdt[t].i, cdt[t].j, N);
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else cdt[t].g = old;
        if (bad < best) {
            best = bad;
            memcpy(sa_best, cdt, sizeof(Dart) * cnd);
            stall = 0;
        } else {
            stall++;
        }
        T *= 0.9995;
        if (T < 0.3) T = 0.3;
        if (stall > STALL_RESET) {
            memcpy(cdt, sa_best, sizeof(Dart) * cnd);
            bad = best;
            T = 2.0;
            stall = 0;
        }
    }
    memcpy(cdt, sa_best, sizeof(Dart) * cnd);
    return best == 0;
}

static void build_lift(Graph *g, int p, int N) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= p * N;
    }
    for (int t = 0; t < cnd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, cdt[t].i * N + x, p * N + cdt[t].j * N + GT[x * N + cdt[t].g]);
}

/* Search lifts of order strictly above the current best; the window ratchets upward. */
static void search(long start_n, double until) {
    static int cb[1024], ck[1024];
    best_n = start_n;
    while (now() < until) {
        long target = best_n + 2;
        if (target > moore) break;
        long hi = target + target / 4 + 60;
        if (hi > moore) hi = moore;
        if (hi > MAXN) hi = MAXN;
        int p = 1 + rndint(MAXP);
        long Nlo = (target + 2 * p - 1) / (2 * p);
        long Nhi = hi / (2 * p);
        if (Nhi > MAXG) Nhi = MAXG;
        if (Nlo < (long)d * p + 1) Nlo = (long)d * p + 1;
        if (Nhi < Nlo) continue;

        int N = 0, ok = 0;
        if (rndint(2) == 0) {
            int cnt = 0;
            for (int b = 0; b < NB; b++) {
                int o = base_ord[b];
                if (!o) continue;
                for (int k = 1; k * o <= MAXG; k++) {
                    long NN = (long)o * k;
                    if (NN >= Nlo && NN <= Nhi && cnt < 1024) {
                        cb[cnt] = b;
                        ck[cnt] = k;
                        cnt++;
                    }
                }
            }
            if (cnt > 0) {
                int c = rndint(cnt);
                set_product(cb[c], ck[c]);
                N = base_ord[cb[c]] * ck[c];
                ok = 1;
            }
        }
        if (!ok) {
            N = (int)(Nlo + rndint((int)(Nhi - Nlo + 1)));
            int m, k, r;
            if (!sample_semidirect(N, &m, &k, &r)) continue;
            set_semidirect(m, k, r);
        }
        if (!lift_sa(p, N, until)) continue;
        build_lift(&tmpg, p, N);
        if (tmpg.n > best_n && is_valid(&tmpg)) {
            bestg = tmpg;
            best_n = tmpg.n;
            have_best = 1;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    init_bases();
    search(start_n, t_end);
    if (have_best && is_valid(&bestg)) print_graph(&bestg);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    A candidate is kept only if it passes lib.is_valid with diameter 6. Returns None if nothing verifies.
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    # Leave margin for compilation, startup and output.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, best[0]],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

"""Bi-Cayley (Haar-type) search over non-abelian groups.

Changes from the parent:
- The voltage-cover and voltage-lift engine is replaced. The new C engine searches bi-Cayley
  graphs. A group G of order N acts regularly on each side, and vertex a_x is joined to b_{x*s}
  for s in a connection set S of d distinct elements. This graph is d-regular and bipartite on
  2N vertices. Left translation is an automorphism, so diameter <= D holds iff BFS from a_0 and
  from b_0 both reach all 2N vertices within D steps. Each evaluation is therefore cheap, about
  2 BFS, so simulated annealing over S can run hundreds of thousands of steps per attempt.
- Groups: semidirect products Z_m x| Z_k for every divisor pair and every valid r, and direct
  products PSL(2,p)/PGL(2,p) x Z_k for p = 5, 7, 11.
- Target orders are a sliding window just above the current best, so a failed order (for
  example a prime, which forces an abelian group) does not block the search.
- Python keeps the algebraic starts (PG(2,q), W(q), H(3), K_{d,d}) and validates every output.
  Any failure returns the best valid graph found so far.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search.
 * Usage:  prog d D seed time_limit start_n   (stdin ignored)
 * Graph: sides A (x in G) and B (y in G); a_x ~ b_{x*s} for s in S, |S| = d.
 * Valid iff BFS from a_0 and from b_0 reach all 2N vertices within D steps.
 * stdout: "n m" then edges, or "0 0" if nothing beats start_n.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXO 1100
#define MAXD 32
#define MAXBG 700
#define MAXCAND 4096
#define HS 8192
#define NBASE 5
#define SA_LEN 60000
#define SA_T0 1.2

static int d, D;
static double t_end;

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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

/* ---------------------------------------------------------------- permutation groups */
typedef struct { unsigned char p[16]; } Perm;
static Perm PE[MAXBG];
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
    memset(&PE[0], 0, sizeof(Perm));
    for (int x = 0; x < p + 1; x++) PE[0].p[x] = (unsigned char)x;
    hput(pkey(PE[0].p, p + 1), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = PE[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXBG) return 0;
                PE[n] = h;
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
            for (int x = 0; x < s; x++) h.p[x] = PE[i].p[PE[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * ord + j] = idx < 0 ? 0 : idx;
        }
    *ordp = ord;
    return tab;
}

static int *base_tab[NBASE];
static int base_ord[NBASE];

static void init_bases(void) {
    static const int BP[NBASE] = {5, 5, 7, 7, 11};
    static const int BG[NBASE] = {0, 1, 0, 1, 0};
    for (int b = 0; b < NBASE; b++) {
        int ord = 0;
        base_tab[b] = make_base_table(BP[b], BG[b], &ord);
        base_ord[b] = base_tab[b] ? ord : 0;
    }
}

/* ---------------------------------------------------------------- group tables */
static int GT[MAXO * MAXO];
static int INV[MAXO];

typedef struct { int type, b, m, k, r; } Cand;
static Cand cands[MAXCAND];
static int ncand = 0;

static void add_cand(int type, int b, int m, int k, int r) {
    if (ncand >= MAXCAND) return;
    cands[ncand].type = type;
    cands[ncand].b = b;
    cands[ncand].m = m;
    cands[ncand].k = k;
    cands[ncand].r = r;
    ncand++;
}

/* Fill GT for candidate c; returns its order. */
static int build_group(const Cand *c) {
    static long rp[MAXO];
    if (c->type == 0) {
        int m = c->m, k = c->k, N = m * k;
        rp[0] = 1 % m;
        for (int b = 1; b < k; b++) rp[b] = rp[b - 1] * c->r % m;
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < N; y++) {
                int cc = y / k, e = y % k;
                GT[x * N + y] = (int)(((a + rp[b] * cc) % m) * k + (b + e) % k);
            }
        }
        return N;
    }
    int o = base_ord[c->b], k = c->k, N = o * k;
    const int *bt = base_tab[c->b];
    for (int x = 0; x < o; x++)
        for (int cc = 0; cc < k; cc++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + cc) * N + (y * k + e)] = bt[x * o + y] * k + (cc + e) % k;
    return N;
}

static int compute_inv(int N) {
    for (int x = 0; x < N; x++) {
        int f = -1;
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { f = y; break; }
        if (f < 0) return 0;
        INV[x] = f;
    }
    return 1;
}

static void make_cands(int N) {
    ncand = 0;
    for (int b = 0; b < NBASE; b++) {
        int o = base_ord[b];
        if (!base_tab[b] || o <= 0 || N % o != 0) continue;
        add_cand(1, b, 0, N / o, 0);
    }
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { add_cand(0, 0, 1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcdl(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            add_cand(0, 0, m, k, r);
        }
    }
}

/* ---------------------------------------------------------------- annealing */
static int Sg[MAXD], SIg[MAXD];
static int Sbest[MAXD];
static int NN;
static int vis[2 * MAXO], dep[2 * MAXO], qu[2 * MAXO];
static int stampc = 0;

static int in_set(int t, int k) {
    for (int i = 0; i < k; i++)
        if (Sg[i] == t) return 1;
    return 0;
}

/* Number of vertices reached from src within D steps. */
static int reach(int src) {
    int N = NN;
    int st = ++stampc;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = st;
    dep[src] = 0;
    while (head < tail) {
        int v = qu[head++];
        if (dep[v] >= D) continue;
        int nd = dep[v] + 1;
        if (v < N) {
            const int *row = GT + (size_t)v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[Sg[i]];
                if (vis[u] != st) { vis[u] = st; dep[u] = nd; qu[tail++] = u; }
            }
        } else {
            const int *row = GT + (size_t)(v - N) * N;
            for (int i = 0; i < d; i++) {
                int u = row[SIg[i]];
                if (vis[u] != st) { vis[u] = st; dep[u] = nd; qu[tail++] = u; }
            }
        }
    }
    return tail;
}

static long evalf(void) {
    int N = NN;
    int a = reach(0);
    int b = reach(N);
    return (long)(2 * N - a) + (long)(2 * N - b);
}

/* Anneal a connection set of size d in the current group (GT and INV must be set).
 * Returns 1 if a valid set was found (stored in Sbest). */
static int sa_attempt(int N, long L, double T0) {
    NN = N;
    for (int i = 0; i < d; i++) {
        int t;
        do t = rndint(N); while (in_set(t, i));
        Sg[i] = t;
        SIg[i] = INV[t];
    }
    long f = evalf();
    long bestf = f;
    memcpy(Sbest, Sg, sizeof(int) * d);
    if (f == 0) return 1;
    double T = T0, fac = pow(0.01, 1.0 / (double)L);
    for (long s = 0; s < L; s++) {
        if ((s & 2047) == 0 && now() > t_end) break;
        int i = rndint(d);
        int old = Sg[i], oldi = SIg[i];
        int t;
        do t = rndint(N); while (in_set(t, d));
        Sg[i] = t;
        SIg[i] = INV[t];
        long nf = evalf();
        if (nf <= f || rnd01() < exp(-(double)(nf - f) / T)) {
            f = nf;
            if (f < bestf) {
                bestf = f;
                memcpy(Sbest, Sg, sizeof(int) * d);
                if (f == 0) return 1;
            }
        } else {
            Sg[i] = old;
            SIg[i] = oldi;
        }
        T *= fac;
    }
    return bestf == 0;
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    init_bases();

    long maxN = moore_bound() / 2;
    if (maxN > MAXO) maxN = MAXO;
    long lo = start_n / 2 + 1;
    if (lo < d + 1) lo = d + 1;

    int have = 0;
    int bestN = 0;
    Cand bestC;
    int bestS[MAXD];
    memset(&bestC, 0, sizeof bestC);

    while (now() < t_end && lo <= maxN) {
        long hi = lo + 7;
        if (hi > maxN) hi = maxN;
        int N = (int)(lo + rndint((int)(hi - lo + 1)));
        make_cands(N);
        if (ncand == 0) continue;
        int ci = rndint(ncand);
        build_group(&cands[ci]);
        if (!compute_inv(N)) continue;
        if (sa_attempt(N, SA_LEN, SA_T0)) {
            have = 1;
            bestN = N;
            bestC = cands[ci];
            memcpy(bestS, Sbest, sizeof(int) * d);
            lo = N + 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int N = build_group(&bestC);
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + GT[x * N + bestS[i]]);
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

    Returns None if no sign convention verifies with lib.is_valid.
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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), int(best[0])],
                         stdin_graph=None, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best

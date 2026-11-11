"""Bi-Cayley (single-orbit) lifts over explicit groups for the weakest target (d=4, D=7).

This replaces the parent's voltage-lift search with a different construction. Each candidate is
a bi-Cayley graph: vertices A_x and B_y for x, y in a finite group G of order N, with A_x adjacent
to B_{x s} for each s in a connection set S of size d. Left multiplication by G is an automorphism
that acts transitively on each side, so the diameter test reduces to two BFS runs, from A_0 and
from B_0, which is exact. The search is simulated annealing over S, and the groups come from
semidirect products Z_m x| Z_k and from direct products PSL(2,p) or PGL(2,p) times Z_k. The
groups for each order N are drawn at random from a window just above the current best order.

Start-up: the Python side still builds the known algebraic starts (PG(2,q), W(q), H(3)) and only
hands the C engine a search for graphs with more vertices than the current best. Every output
is re-checked with lib.is_valid, and if anything fails or nothing better is found, the best
valid graph built so far is returned.

This is a high-risk experiment. There is no guarantee it beats the 840-vertex record.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search.
 * Usage: prog d D seed time_limit minn   (stdin ignored)
 * Output: "n m" and m edges for the largest graph found with n > minn, or "0 0".
 *
 * Graph on 2N vertices (N = |G|): A_x = x, B_y = N + y, with A_x ~ B_{x*s} for s in S (|S| = d).
 * Left multiplication is an automorphism, so the diameter condition is exactly:
 * every vertex is within distance D of A_0 and of B_0.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1400
#define MAXV (2 * MAXG)
#define MAXD 16
#define HS 8192
#define NBASE 5
#define MAXOPT 8192

static int d, D;
static long minn;
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

/* ---------------------------------------------------------------- permutation groups */
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

/* Closure of PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) acting on P^1(F_p). */
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

static const int BP[NBASE] = {5, 5, 7, 7, 11};
static const int BG[NBASE] = {0, 1, 0, 1, 0};
static int *BT[NBASE];
static int BO[NBASE];

static void init_bases(void) {
    for (int b = 0; b < NBASE; b++) {
        BT[b] = NULL;
        BO[b] = 0;
        int ord = 0;
        if (!perm_closure(BP[b], BG[b], &ord)) continue;
        int s = BP[b] + 1;
        int *tab = malloc(sizeof(int) * (size_t)ord * (size_t)ord);
        if (!tab) continue;
        for (int i = 0; i < ord; i++)
            for (int j = 0; j < ord; j++) {
                Perm h;
                memset(&h, 0, sizeof h);
                for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
                int idx = hfind(pkey(h.p, s));
                tab[(size_t)i * ord + j] = idx < 0 ? 0 : idx;
            }
        BT[b] = tab;
        BO[b] = ord;
    }
}

/* ---------------------------------------------------------------- group tables */
static int GN;
static int GT[MAXG * MAXG];   /* GT[x*GN + y] = x*y, identity 0 */
static int invv[MAXG];

/* Z_m x|_r Z_k: (a,b)(c,e) = (a + r^b c, b + e), element a*k + b. */
static void set_semidirect(int m, int k, int r) {
    int N = m * k;
    static int rp[MAXG];
    GN = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)(((a1 + (long)rp[b1] * c) % m) * k + (b1 + e) % k);
        }
    }
}

/* Base permutation group times Z_k: element x*k + c. */
static void set_perm_product(int b, int k) {
    int o = BO[b], N = o * k;
    GN = N;
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] = BT[b][x * o + y] * k + (c + e) % k;
}

static void compute_inverses(void) {
    int N = GN;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { invv[x] = y; break; }
}

/* ---------------------------------------------------------------- group options */
typedef struct { int kind, x, k, r; } Opt;
static Opt opts[MAXOPT];
static int nopt, nsd;

static void add_opt(int kind, int x, int k, int r) {
    if (nopt < MAXOPT) {
        opts[nopt].kind = kind;
        opts[nopt].x = x;
        opts[nopt].k = k;
        opts[nopt].r = r;
        nopt++;
    }
}

static void enumerate_opts(int N) {
    nopt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { add_opt(0, 1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            add_opt(0, m, k, r);
        }
    }
    nsd = nopt;
    for (int b = 0; b < NBASE; b++)
        if (BO[b] > 0 && N % BO[b] == 0) add_opt(1, b, N / BO[b], 0);
}

static void set_opt(const Opt *o) {
    if (o->kind == 0) set_semidirect(o->x, o->k, o->r);
    else set_perm_product(o->x, o->k);
}

/* ---------------------------------------------------------------- bi-Cayley search */
static int S[MAXD];
static int seenst[MAXV], dq[MAXV], qb[MAXV];
static int stampc = 0;

static int contains(int g, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == g) return 1;
    return 0;
}

static inline int nbr(int v, int i) {
    if (v < GN) return GN + GT[v * GN + S[i]];
    return GT[(v - GN) * GN + invv[S[i]]];
}

static int reach_from(int src) {
    stampc++;
    int head = 0, tail = 0;
    seenst[src] = stampc;
    dq[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        if (dq[v] >= D) continue;
        for (int i = 0; i < d; i++) {
            int u = nbr(v, i);
            if (seenst[u] != stampc) {
                seenst[u] = stampc;
                dq[u] = dq[v] + 1;
                qb[tail++] = u;
            }
        }
    }
    return tail;
}

static long badcount(void) {
    int V = 2 * GN;
    return (long)(V - reach_from(0)) + (long)(V - reach_from(GN));
}

static int sa_attempt(int steps) {
    int N = GN;
    for (int i = 0; i < d; i++) {
        do S[i] = rndint(N); while (contains(S[i], i));
    }
    long bad = badcount();
    double T = 1.5;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        int i = rndint(d);
        int old = S[i];
        int g;
        do g = rndint(N); while (contains(g, d));
        S[i] = g;
        long nb = badcount();
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) bad = nb;
        else S[i] = old;
        T *= 0.9995;
        if (T < 0.08) T = 0.08;
    }
    return bad == 0;
}

static int bestE[MAXG * MAXD * 2];
static int bestNv = 0, bestM = 0;

static void record(int N) {
    int m = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            bestE[2 * m] = x;
            bestE[2 * m + 1] = N + GT[x * N + S[i]];
            m++;
        }
    bestNv = 2 * N;
    bestM = m;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit minn\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    minn = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long mb = 0, pw = 1;
    for (int i = 0; i < D && mb < 1000000; i++) { mb += pw; pw *= (d - 1); }
    long moore = 2 * mb;
    long Nmax = moore / 2;
    if (Nmax > MAXG) Nmax = MAXG;
    long nlo = minn / 2 + 1;
    if (nlo < d) nlo = d;
    if (nlo > Nmax) { printf("0 0\n"); return 0; }

    init_bases();

    while (now() < t_end && nlo <= Nmax) {
        long hi = nlo + nlo / 6 + 25;
        if (hi > Nmax) hi = Nmax;
        int N = (int)(nlo + rndint((int)(hi - nlo + 1)));
        enumerate_opts(N);
        if (nopt == 0) continue;
        int nperm = nopt - nsd;
        int pick;
        if (nperm > 0 && (nsd == 0 || rndint(2) == 0)) pick = nsd + rndint(nperm);
        else pick = rndint(nsd);
        set_opt(&opts[pick]);
        compute_inverses();
        for (int a = 0; a < 4 && now() < t_end; a++) {
            if (sa_attempt(4000)) {
                record(N);
                nlo = N + 1;
                break;
            }
        }
    }

    if (bestNv > 0) {
        printf("%d %d\n", bestNv, bestM);
        for (int i = 0; i < bestM; i++)
            printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
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

    A candidate is kept only if it passes lib.is_valid with diameter 6. Returns None otherwise.
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
        starts = known_starts(d, D)
    except Exception:
        starts = []
    for n, e in starts:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best

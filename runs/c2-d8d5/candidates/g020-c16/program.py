"""Bold variant: bi-Cayley lifts over matrix groups PGL/PSL/Borel(2,p), searched in C.

The base graph is a union of d perfect matchings between k blocks, each block a copy of
a finite group G. Edges are A_{i,x} ~ B_{j,x*s}. Left multiplication by G is an automorphism,
so diameter only needs BFS from one representative per block. The ladder climbs through
candidate orders, keeping every success. Exact constructions and K_{d,d} stay as fallbacks.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (kept from the parent program).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
# C engine: bi-Cayley lifts over matrix groups (PGL(2,p), PSL(2,p), Borel of PGL(2,p)).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley search over finite matrix groups.
 * Usage: prog d D seed time_limit   (stdin ignored)
 * Vertices: A_{i,x} = i*G + x, B_{j,y} = (K+j)*G + y.
 * Layer l matches A_i to B_{lay[l][i]} with voltage vol[l][i]: A_{i,x} ~ B_{j,x*s}.
 * Left multiplication is an automorphism, so BFS from one representative per block
 * (vertex r*G, r < 2K) decides the diameter.
 * stdout: "n m" then m edges, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 12000
#define MAXD 16
#define MAXK 8
#define MAXG 6100
#define MAXP4 279841
#define MAXE 200000
#define MAXC 512

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

/* ---------------- group: 2x2 matrices over F_p, normalized projectively ---------------- */

static int P, G;
static int gel[MAXG][4];
static int gin[MAXG];
static int idxmap[MAXP4];
static int invt[32];

static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = ((b % m) + m) % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int code_of(const int *m) { return ((m[0] * P + m[1]) * P + m[2]) * P + m[3]; }

static void normalize4(int *m) {
    int t = 0;
    while (t < 4 && m[t] == 0) t++;
    if (t == 4) return;
    int f = invt[m[t]];
    for (int s = 0; s < 4; s++) m[s] = (m[s] * f) % P;
}

static int gmul(int x, int y) {
    const int *A = gel[x], *B = gel[y];
    int m[4];
    m[0] = (A[0] * B[0] + A[1] * B[2]) % P;
    m[1] = (A[0] * B[1] + A[1] * B[3]) % P;
    m[2] = (A[2] * B[0] + A[3] * B[2]) % P;
    m[3] = (A[2] * B[1] + A[3] * B[3]) % P;
    normalize4(m);
    return idxmap[code_of(m)];
}

/* fam 0: PGL(2,p), fam 1: PSL(2,p) (det a square), fam 2: Borel (c = 0). */
static int build_group(int p, int fam) {
    P = p;
    G = 0;
    int P4 = p * p * p * p;
    for (int c = 0; c < P4; c++) idxmap[c] = -1;
    for (int x = 1; x < p; x++) invt[x] = powmod_i(x, p - 2, p);
    for (int a = 0; a < p; a++)
    for (int b = 0; b < p; b++)
    for (int c = 0; c < p; c++)
    for (int e = 0; e < p; e++) {
        int m[4] = {a, b, c, e};
        int det = ((a * e - b * c) % p + p) % p;
        if (!det) continue;
        int t = 0;
        while (t < 4 && m[t] == 0) t++;
        if (t == 4 || m[t] != 1) continue;
        if (fam == 1 && powmod_i(det, (p - 1) / 2, p) != 1) continue;
        if (fam == 2 && c != 0) continue;
        if (G >= MAXG) return 0;
        memcpy(gel[G], m, sizeof m);
        idxmap[code_of(m)] = G;
        G++;
    }
    for (int x = 0; x < G; x++) {
        const int *A = gel[x];
        int m[4] = {A[3], (p - A[1]) % p, (p - A[2]) % p, A[0]};
        normalize4(m);
        gin[x] = idxmap[code_of(m)];
    }
    return G;
}

/* ---------------- lift state ---------------- */

static int K, NV;
static int lay[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int nbr[MAXV][MAXD];

static void set_dart(int l, int i) {
    int j = lay[l][i], s = vol[l][i];
    for (int x = 0; x < G; x++) {
        int y = gmul(x, s);
        int a = i * G + x;
        int b = (K + j) * G + y;
        nbr[a][l] = b;
        nbr[b][l] = a;
    }
}

static int dup_free(void) {
    for (int i = 0; i < K; i++)
    for (int a = 0; a < d; a++)
    for (int b = a + 1; b < d; b++)
        if (lay[a][i] == lay[b][i] && vol[a][i] == vol[b][i]) return 0;
    return 1;
}

static void init_state(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l][i] = perm[i];
            vol[l][i] = rndint(G);
        }
    }
    long guard = 0;
    while (!dup_free() && guard++ < 10000000L)
        vol[rndint(d)][rndint(K)] = rndint(G);
}

/* ---------------- cost: unreached pairs from the 2K block representatives ---------------- */

static int vis[MAXV];
static int stamp = 0;
static int queue[MAXV];

static long eval_cost(void) {
    long cost = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        int head = 0, tail = 0;
        queue[tail++] = src;
        vis[src] = stamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = queue[head++];
                for (int l = 0; l < d; l++) {
                    int u = nbr[v][l];
                    if (vis[u] != stamp) {
                        vis[u] = stamp;
                        queue[tail++] = u;
                    }
                }
            }
        }
        cost += NV - tail;
    }
    return cost;
}

/* ---------------- annealing trial ---------------- */

static int run_trial(double until) {
    init_state();
    if (!dup_free()) return 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
    long cost = eval_cost();
    if (cost == 0) return 1;
    double t_start = now();
    double T0 = 0.5 + 0.02 * (double)cost;
    double T = T0;
    long bestc = cost, stall = 0, it = 0;
    const long maxstall = 150000;
    for (;;) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn > until) break;
            double frac = (tn - t_start) / (until - t_start + 1e-9);
            if (frac > 1.0) frac = 1.0;
            T = T0 * (1.0 - frac) + 0.05;
        }
        it++;
        if (++stall > maxstall) break;
        int l = rndint(d), i = rndint(K);
        if (K >= 2 && rnd01() < 0.3) {
            int i2 = rndint(K);
            if (i2 == i) continue;
            int tmp = lay[l][i]; lay[l][i] = lay[l][i2]; lay[l][i2] = tmp;
            if (!dup_free()) {
                tmp = lay[l][i]; lay[l][i] = lay[l][i2]; lay[l][i2] = tmp;
                continue;
            }
            set_dart(l, i);
            set_dart(l, i2);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = lay[l][i]; lay[l][i] = lay[l][i2]; lay[l][i2] = tmp;
                set_dart(l, i);
                set_dart(l, i2);
            }
        } else {
            int old = vol[l][i];
            int g = rndint(G);
            if (g == old) continue;
            vol[l][i] = g;
            if (!dup_free()) { vol[l][i] = old; continue; }
            set_dart(l, i);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                vol[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; stall = 0; }
        if (cost == 0) return 1;
    }
    return cost == 0;
}

/* ---------------- best graph and candidate ladder ---------------- */

static int bestN = 0, bestM = 0;
static int bu[MAXE], bv[MAXE];

static void set_complete(int dd) {
    bestN = 2 * dd;
    bestM = 0;
    for (int a = 0; a < dd; a++)
        for (int b = 0; b < dd; b++) {
            bu[bestM] = a;
            bv[bestM] = dd + b;
            bestM++;
        }
}

static void store_best(void) {
    bestN = NV;
    bestM = 0;
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) {
            bu[bestM] = v;
            bv[bestM] = nbr[v][l];
            bestM++;
        }
}

static void print_best(void) {
    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
}

typedef struct { int p, fam, k, G, N; } Cand;
static Cand cand[MAXC];
static int ncand = 0;

static void make_cands(void) {
    static const int primes[8] = {3, 5, 7, 11, 13, 17, 19, 23};
    ncand = 0;
    for (int pi = 0; pi < 8; pi++)
    for (int fam = 0; fam < 3; fam++)
    for (int k = 1; k <= MAXK; k++) {
        long p = primes[pi];
        long Gs = fam == 0 ? p * (p * p - 1) : fam == 1 ? p * (p * p - 1) / 2 : p * (p - 1);
        long N = 2L * k * Gs;
        if (N > MAXV || Gs > MAXG || (long)k * Gs < d) continue;
        if (ncand >= MAXC) continue;
        cand[ncand].p = (int)p;
        cand[ncand].fam = fam;
        cand[ncand].k = k;
        cand[ncand].G = (int)Gs;
        cand[ncand].N = (int)N;
        ncand++;
    }
    for (int i = 1; i < ncand; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit * 0.95;

    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    set_complete(d);
    if (D < 2) { printf("0 0\n"); return 0; }
    if (D == 2) { print_best(); return 0; }

    make_cands();
    int cur_p = -1, cur_f = -1;
    while (now() < t_end) {
        int first = ncand;
        for (int c = 0; c < ncand; c++)
            if (cand[c].N >= bestN + 2) { first = c; break; }
        if (first >= ncand) break;
        int avail = ncand - first;
        int span = avail < 6 ? avail : 6;
        int pick = rndint(100) < 60 ? first : first + rndint(span);
        Cand c = cand[pick];
        if (c.p != cur_p || c.fam != cur_f) {
            if (!build_group(c.p, c.fam)) break;
            cur_p = c.p;
            cur_f = c.fam;
        }
        if (2 * c.k * G != c.N) break;
        K = c.k;
        NV = 2 * K * G;
        double rem = t_end - now();
        if (rem <= 0) break;
        double slice = rem / 3.0;
        if (slice < 1.0) slice = rem;
        if (run_trial(now() + slice)) store_best();
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Matrix-group bi-Cayley search in C.
    if 3 <= D and d <= 16:
        usable = max(1.0, 0.85 * time_limit - 2.0)
        budget = round(usable - (time.monotonic() - t0) - 0.5, 2)
        if budget >= 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                                 stdin_graph=None, timeout=budget + 10)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

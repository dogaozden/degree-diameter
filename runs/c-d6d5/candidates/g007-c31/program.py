"""Bi-Cayley / small-base lift search with full-neighbourhood tabu search.

Different from the annealing lift search: each graph is a lift of a base with K vertices per side
over a finite group G of order M*K2 (Z_M x| Z_K2, the semidirect product with multiplier R).
Vertices are A(i,x) and B(j,y) with x, y in G. Each of DEG layers is a permutation P_l of the K
blocks, and dart (l,i) carries a voltage s in G, joining A(i,x) to B(P_l(i), x*s).
The lift is then DEG-regular and bipartite. Left multiplication by G is an automorphism, so
2K BFS runs from block identities decide the diameter exactly.

Search: a tabu search over single-voltage changes and within-layer target swaps. Each step samples a
batch of candidate moves, takes the best non-tabu one (with aspiration), and restarts after a stall.
The target order is the best known bar, which rises on every success. Groups are drawn at random
just above the bar, across several group orders and block counts K.

Python: K_{d,d} fallback, known D = 3 constructions, W(q) for D >= 4, and final validation with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDEG 40
#define MAXK 3
#define MAXG 3000
#define MAXCELL (MAXDEG * MAXK)
#define MAXN (2 * MAXK * MAXG)
#define CAND 48
#define DUPPEN 1000000LL
#define HUGECOST 4000000000000LL

static int DEG, DIAM;
static double END_T;
static struct timespec T0;
static uint64_t rs[2];

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group */

static int K, G, GM, GK2, GR;   /* G = GM * GK2, element a*GK2 + b */
static int *MT = NULL;          /* MT[x*G + y] = x*y */
static int MTcap = 0;

static void build_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GR = r;
    G = m * k2;
    if (G * G > MTcap) {
        free(MT);
        MTcap = G * G;
        MT = malloc(sizeof(int) * (size_t)MTcap);
    }
    int *rp = malloc(sizeof(int) * (size_t)k2);
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long long)rp[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int ra = (int)(((long long)a + (long long)rp[b] * c) % m);
            int rb = (b + e) % k2;
            MT[x * G + y] = ra * k2 + rb;
        }
    }
    free(rp);
}

/* ------------------------------------------------------------ configuration */

static int NCELL;                 /* DEG * K cells; cell c = l*K + i */
static int P[MAXCELL], S[MAXCELL];   /* target block and voltage */
static int outP[MAXCELL], outS[MAXCELL];
static int rbP[MAXCELL], rbS[MAXCELL];
static int tabu_until[MAXCELL];

static int *adjA, *fillc, *stampA, *qbuf;
static int stampcur = 0;

static long long eval_cost(void) {
    int T = NCELL, N = 2 * K * G;
    long long pen = 0;
    for (int c1 = 0; c1 < T; c1++)
        for (int c2 = c1 + K; c2 < T; c2 += K)
            if (P[c1] == P[c2] && S[c1] == S[c2]) pen += DUPPEN;
    if (pen) return pen;

    for (int v = 0; v < N; v++) fillc[v] = 0;
    for (int c = 0; c < T; c++) {
        int i = c % K, j = P[c], s = S[c];
        int bbase = K * G + j * G;
        for (int x = 0; x < G; x++) {
            int a = i * G + x;
            int b = bbase + MT[x * G + s];
            adjA[(size_t)a * DEG + fillc[a]++] = b;
            adjA[(size_t)b * DEG + fillc[b]++] = a;
        }
    }

    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = (r < K) ? r * G : K * G + (r - K) * G;
        stampcur++;
        if (stampcur >= 0x7fffffff) {
            memset(stampA, 0, sizeof(int) * (size_t)MAXN);
            stampcur = 1;
        }
        int tail = 0;
        qbuf[tail++] = src;
        stampA[src] = stampcur;
        int ls = 0, le = 1;
        for (int dd = 0; dd < DIAM && ls < le; dd++) {
            for (int q = ls; q < le; q++) {
                const int *au = adjA + (size_t)qbuf[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int u = au[e];
                    if (stampA[u] != stampcur) {
                        stampA[u] = stampcur;
                        qbuf[tail++] = u;
                    }
                }
            }
            ls = le;
            le = tail;
        }
        total += N - tail;
    }
    return total;
}

static void random_config(void) {
    int p[MAXK];
    NCELL = DEG * K;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            P[l * K + i] = p[i];
            S[l * K + i] = rnd_int(G);
        }
    }
}

/* Tabu search over single-voltage changes and within-layer target swaps.
 * Returns the best cost reached; P,S are left at that best configuration. */
static long long run_tabu(double until, long long stall) {
    int T = NCELL;
    long long cur = eval_cost();
    long long runBest = cur;
    memcpy(rbP, P, sizeof(int) * (size_t)T);
    memcpy(rbS, S, sizeof(int) * (size_t)T);
    for (int c = 0; c < T; c++) tabu_until[c] = 0;
    long long noimp = 0, step = 0;

    while (cur > 0 && noimp < stall) {
        if ((step & 7) == 0 && now_s() > until) break;
        step++;
        int ntype[CAND], na[CAND], nb[CAND], nv[CAND], nt[CAND];
        long long nc[CAND];
        int nn = 0;
        for (int k = 0; k < CAND; k++) {
            if (K > 1 && rnd_unit() < 0.3) {
                int l = rnd_int(DEG);
                int i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int c1 = l * K + i1, c2 = l * K + i2;
                int tmp = P[c1]; P[c1] = P[c2]; P[c2] = tmp;
                long long cc = eval_cost();
                tmp = P[c1]; P[c1] = P[c2]; P[c2] = tmp;
                ntype[nn] = 1;
                na[nn] = c1;
                nb[nn] = c2;
                nv[nn] = 0;
                nc[nn] = cc;
                nt[nn] = (tabu_until[c1] > step) || (tabu_until[c2] > step);
                nn++;
            } else {
                int c = rnd_int(T);
                int nval = rnd_int(G);
                if (nval == S[c]) continue;
                int old = S[c];
                S[c] = nval;
                long long cc = eval_cost();
                S[c] = old;
                ntype[nn] = 0;
                na[nn] = c;
                nb[nn] = 0;
                nv[nn] = nval;
                nc[nn] = cc;
                nt[nn] = tabu_until[c] > step;
                nn++;
            }
        }
        if (nn == 0) continue;

        int bi = -1;
        for (int k = 0; k < nn; k++) {
            int allowed = (!nt[k]) || (nc[k] < runBest);
            if (!allowed) continue;
            if (bi < 0 || nc[k] < nc[bi] || (nc[k] == nc[bi] && rnd_int(2))) bi = k;
        }
        if (bi < 0) bi = rnd_int(nn);

        int tenure = 3 + rnd_int(6);
        if (ntype[bi] == 1) {
            int c1 = na[bi], c2 = nb[bi];
            int tmp = P[c1]; P[c1] = P[c2]; P[c2] = tmp;
            tabu_until[c1] = (int)(step + tenure);
            tabu_until[c2] = (int)(step + tenure);
        } else {
            S[na[bi]] = nv[bi];
            tabu_until[na[bi]] = (int)(step + tenure);
        }
        cur = nc[bi];
        if (cur < runBest) {
            runBest = cur;
            memcpy(rbP, P, sizeof(int) * (size_t)T);
            memcpy(rbS, S, sizeof(int) * (size_t)T);
            noimp = 0;
        } else {
            noimp++;
        }
    }
    memcpy(P, rbP, sizeof(int) * (size_t)T);
    memcpy(S, rbS, sizeof(int) * (size_t)T);
    return runBest;
}

/* ------------------------------------------------------------ output */

static int bFound = 0, bK = 0, bGM = 0, bGK2 = 0, bGR = 0;

static void print_best(void) {
    if (!bFound) {
        printf("0 0\n");
        return;
    }
    K = bK;
    build_group(bGM, bGK2, bGR);
    NCELL = DEG * K;
    memcpy(P, outP, sizeof(int) * (size_t)NCELL);
    memcpy(S, outS, sizeof(int) * (size_t)NCELL);
    if (eval_cost() != 0) {
        printf("0 0\n");
        return;
    }
    int N = 2 * K * G;
    printf("%d %d\n", N, DEG * K * G);
    for (int c = 0; c < NCELL; c++) {
        int i = c % K, j = P[c], s = S[c];
        for (int x = 0; x < G; x++)
            printf("%d %d\n", i * G + x, K * G + j * G + MT[x * G + s]);
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [bar]\n");
        return 2;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    END_T = atof(argv[4]);
    int bar = (argc >= 6) ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (bar < 2 * DEG) bar = 2 * DEG;

    uint64_t sm = sd * 0x9E3779B97F4A7C15ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    adjA = malloc(sizeof(int) * (size_t)MAXN * MAXDEG);
    fillc = malloc(sizeof(int) * (size_t)MAXN);
    stampA = calloc((size_t)MAXN, sizeof(int));
    qbuf = malloc(sizeof(int) * (size_t)MAXN);

    while (now_s() < END_T) {
        double u = rnd_unit();
        K = (u < 0.4) ? 1 : ((u < 0.75) ? 2 : 3);
        int Gmin = bar / (2 * K) + 1;
        if (Gmin < 2) Gmin = 2;
        if (Gmin > MAXG) Gmin = MAXG;
        int g = Gmin + rnd_int(1 + Gmin / 30);
        if (g > MAXG) g = MAXG;

        int divs[32], nd = 0;
        for (int k2 = 1; k2 <= 12 && k2 <= g; k2++)
            if (g % k2 == 0 && g / k2 >= 2) divs[nd++] = k2;
        int k2 = divs[rnd_int(nd)];
        int m = g / k2, r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod_i(cand, k2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                k2 = 1;
                m = g;
                r = 1;
            }
        }

        build_group(m, k2, r);
        random_config();
        double until = now_s() + 4.0;
        if (until > END_T) until = END_T;
        long long res = run_tabu(until, 1500);
        if (res == 0 && eval_cost() == 0) {
            bFound = 1;
            bK = K;
            bGM = m;
            bGK2 = k2;
            bGR = r;
            memcpy(outP, P, sizeof(int) * (size_t)NCELL);
            memcpy(outS, S, sizeof(int) * (size_t)NCELL);
            bar = 2 * K * G;
        }
    }

    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: known constructions and fallbacks.
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _known_start(d, D):
    """Best construction Python builds directly for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = (1, [])
    kd = lib.haar_graph(d, range(d))
    if lib.is_valid(kd[0], kd[1], d, D):
        best = kd

    known = _known_start(d, D)
    if known is not None and known[0] > best[0] and lib.is_valid(known[0], known[1], d, D):
        best = known

    # D >= 4: generalized quadrangle baseline (cheap, guarded by time).
    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.82 * time_limit - (time.monotonic() - t0) - 2.0
    if remaining >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best[0]],
                            stdin_graph=None, timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass  # keep the valid fallback

    return best

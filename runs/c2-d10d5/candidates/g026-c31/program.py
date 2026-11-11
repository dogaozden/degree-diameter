import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: bi-Cayley (voltage) lifts over finite MATRIX groups.
#
# Groups: SL(2,p), PSL(2,p), GL(2,p), PGL(2,p), ASL(2,p) (3x3 affine), for small
# primes p. These are non-metacyclic groups (PSL, ASL, SL, GL are not
# semidirect products of cyclic groups), so they give orders the parent's
# Z_m x| Z_k search never samples.
#
# Lift model: base has K vertices per side (K <= 4) and DEG layers. Layer l is
# a permutation sigma_l of {0..K-1} with a voltage v[l][i] in G. Vertex (A,i,x)
# joins (B,sigma_l(i), x*v[l][i]). Left multiplication by G is an automorphism,
# so the diameter condition reduces to one BFS from each of the 2K base vertices:
# cost = total unreached vertices over those BFS + penalty for duplicate edges.
# That makes one evaluation O(K * N * DEG), far cheaper than all-pairs checks.
#
# Search: simulated annealing over permutations and voltages (layer swap,
# voltage exchange across layers, single voltage change, product voltage),
# with random restarts over (K, group) pairs whose order gives more vertices
# than the current best.
#
# Python: the exact constructions (PG(2,q), W(q)) and K_{d,d} are kept as the
# valid fallback. The C result is accepted only after lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define GMAX 3600
#define NMAX (2 * MAXK * GMAX)
#define MAXDEG 16
#define PEN 1000
#define NCANDMAX 128
#define ITERS 6000
#define PATIENCE 2000

enum { T_SL = 0, T_PSL = 1, T_GL = 2, T_PGL = 3, T_ASL = 4 };

typedef struct { int type, p, order; } Cand;
static Cand cands[NCANDMAX];
static int ncand = 0;

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double tstart, TL;
static int timed_out = 0;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static double elapsed(void) { return now_s() - tstart; }

/* ---------------- matrix groups over GF(p) ---------------- */

static int nmat(int type) { return type == T_ASL ? 3 : 2; }

static int ipow(int b, int e) {
    int r = 1;
    while (e-- > 0) r *= b;
    return r;
}

static int md(int x, int p) {
    x %= p;
    return x < 0 ? x + p : x;
}

static int inv_mod(int a, int p) {
    long long r = 1, b = md(a, p), e = p - 2;
    while (e > 0) {
        if (e & 1) r = r * b % p;
        b = b * b % p;
        e >>= 1;
    }
    return (int)r;
}

static void decode(int c, int E, int p, int *M) {
    for (int k = 0; k < 9; k++) M[k] = 0;
    for (int k = 0; k < E; k++) {
        M[k] = c % p;
        c /= p;
    }
}

static int encode(const int *M, int E, int p) {
    int c = 0;
    for (int k = E - 1; k >= 0; k--) c = c * p + M[k];
    return c;
}

static int detA(int type, const int *M, int p) {
    if (type == T_ASL) return md(M[0] * M[4] - M[1] * M[3], p);
    return md(M[0] * M[3] - M[1] * M[2], p);
}

static int is_element(int type, const int *M, int p) {
    int d = detA(type, M, p);
    switch (type) {
    case T_SL:
    case T_PSL: return d == 1;
    case T_GL:
    case T_PGL: return d != 0;
    case T_ASL: return M[6] == 0 && M[7] == 0 && M[8] == 1 && d == 1;
    }
    return 0;
}

/* Canonical representative of the coset M * scalars (PGL) or {M, -M} (PSL). */
static void canon(int type, const int *M, int p, int *out) {
    int E = nmat(type) * nmat(type);
    memcpy(out, M, sizeof(int) * 9);
    if (type == T_PSL) {
        int N[9] = {0};
        for (int k = 0; k < E; k++) N[k] = md(-M[k], p);
        if (encode(N, E, p) < encode(M, E, p)) memcpy(out, N, sizeof(int) * 9);
    } else if (type == T_PGL) {
        int first = -1;
        for (int k = 0; k < 4; k++) {
            if (M[k]) {
                first = k;
                break;
            }
        }
        if (first >= 0 && M[first] != 1) {
            int iv = inv_mod(M[first], p);
            for (int k = 0; k < 4; k++) out[k] = md(M[k] * iv, p);
        }
    }
}

static void mat_mul(int type, const int *a, const int *b, int p, int *out) {
    int n = nmat(type);
    for (int r = 0; r < n; r++)
        for (int c = 0; c < n; c++) {
            int s = 0;
            for (int k = 0; k < n; k++) s += a[r * n + k] * b[k * n + c];
            out[r * n + c] = s % p;
        }
    for (int k = n * n; k < 9; k++) out[k] = 0;
}

static int count_order(int type, int p) {
    int n = nmat(type), E = n * n;
    int tot = ipow(p, E);
    int M[9], C[9], cnt = 0;
    for (int c = 0; c < tot; c++) {
        decode(c, E, p, M);
        if (!is_element(type, M, p)) continue;
        canon(type, M, p, C);
        if (encode(C, E, p) == c) cnt++;
    }
    return cnt;
}

static void build_cands(void) {
    static const int primes[] = {2, 3, 5, 7, 11, 13, 17, 19};
    ncand = 0;
    for (int type = 0; type <= T_ASL; type++)
        for (int pi = 0; pi < 8; pi++) {
            int p = primes[pi];
            if (type == T_PSL && p == 2) continue;
            if (type == T_ASL && p > 5) continue;
            int ord = count_order(type, p);
            if (ord >= 2 && ord <= GMAX && ncand < NCANDMAX) {
                cands[ncand].type = type;
                cands[ncand].p = p;
                cands[ncand].order = ord;
                ncand++;
            }
        }
    for (int i = 1; i < ncand; i++) {
        Cand t = cands[i];
        int j = i - 1;
        while (j >= 0 && cands[j].order > t.order) {
            cands[j + 1] = cands[j];
            j--;
        }
        cands[j + 1] = t;
    }
}

/* Group tables: elements 0..G-1, product TT[x*G+y], inverse INVA, identity ID0. */
static int MATS[GMAX * 9];
static uint16_t TT[GMAX * GMAX];
static int INVA[GMAX];
static int ID0 = 0, G = 0, curcand = -1;

static int build_group(int ci) {
    if (ci == curcand) return 1;
    curcand = -1;
    int type = cands[ci].type, p = cands[ci].p;
    int n = nmat(type), E = n * n;
    int tot = ipow(p, E);
    int *map = malloc(sizeof(int) * (size_t)tot);
    if (!map) return 0;
    for (int c = 0; c < tot; c++) map[c] = -1;
    int M[9], C[9], P[9];
    int g = 0;
    for (int c = 0; c < tot; c++) {
        decode(c, E, p, M);
        if (!is_element(type, M, p)) continue;
        canon(type, M, p, C);
        if (encode(C, E, p) != c) continue;
        if (g >= GMAX) {
            free(map);
            return 0;
        }
        map[c] = g;
        memcpy(MATS + g * 9, M, sizeof(int) * 9);
        g++;
    }
    int Gn = g;
    for (int x = 0; x < Gn; x++)
        for (int y = 0; y < Gn; y++) {
            mat_mul(type, MATS + x * 9, MATS + y * 9, p, P);
            canon(type, P, p, C);
            int idx = map[encode(C, E, p)];
            if (idx < 0) {
                free(map);
                return 0;
            }
            TT[x * Gn + y] = (uint16_t)idx;
        }
    int I[9] = {0};
    for (int r = 0; r < n; r++) I[r * n + r] = 1;
    canon(type, I, p, C);
    int id = map[encode(C, E, p)];
    free(map);
    if (id < 0) return 0;
    ID0 = id;
    for (int x = 0; x < Gn; x++) {
        INVA[x] = -1;
        for (int y = 0; y < Gn; y++)
            if (TT[x * Gn + y] == ID0) {
                INVA[x] = y;
                break;
            }
        if (INVA[x] < 0) return 0;
    }
    G = Gn;
    curcand = ci;
    return 1;
}

/* ---------------- lift state and cost ---------------- */

static int DEG, DIAM, CAP;
static int K = 1, N = 0;
static int lay[MAXDEG * MAXK], vol[MAXDEG * MAXK], backl[MAXDEG * MAXK];
static int NBR[NMAX * MAXDEG];
static int BESTNBR[NMAX * MAXDEG];
static int VIS[NMAX], QU[NMAX];
static int stampc = 0;
static int bestN = 0, bestK = 0, bestG = 0, have_best = 0;
static int64_t curc = 0;

static void fix_back(int l) {
    for (int i = 0; i < K; i++) backl[l * K + lay[l * K + i]] = i;
}

static void build_adj(void) {
    for (int i = 0; i < K; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < DEG; l++) {
                int e = l * K + i;
                int j = lay[e];
                NBR[v * DEG + l] = (K + j) * G + (int)TT[x * G + vol[e]];
            }
        }
    for (int j = 0; j < K; j++)
        for (int y = 0; y < G; y++) {
            int w = (K + j) * G + y;
            for (int l = 0; l < DEG; l++) {
                int i = backl[l * K + j];
                int g = INVA[vol[l * K + i]];
                NBR[w * DEG + l] = i * G + (int)TT[y * G + g];
            }
        }
}

static int dupcount(void) {
    int d = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l2 * K + i] == lay[l * K + i] && vol[l2 * K + i] == vol[l * K + i]) d++;
    return d;
}

static int64_t cost_eval(void) {
    build_adj();
    int64_t tot = 0;
    for (int r = 0; r < 2 * K; r++) {
        int root = r < K ? r * G + ID0 : (K + (r - K)) * G + ID0;
        stampc++;
        int tail = 0;
        QU[tail++] = root;
        VIS[root] = stampc;
        int fs = 0, fe = 1;
        for (int dd = 0; dd < DIAM && fs < fe; dd++) {
            for (int qi = fs; qi < fe; qi++) {
                int v = QU[qi];
                const int *nb = NBR + v * DEG;
                for (int l = 0; l < DEG; l++) {
                    int w = nb[l];
                    if (VIS[w] != stampc) {
                        VIS[w] = stampc;
                        QU[tail++] = w;
                    }
                }
            }
            fs = fe;
            fe = tail;
        }
        tot += N - tail;
    }
    return tot + (int64_t)PEN * dupcount();
}

static void random_init(void) {
    for (int l = 0; l < DEG; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
        fix_back(l);
    }
    for (int e = 0; e < DEG * K; e++) vol[e] = rndint(G);
}

static int run_trial(int iters, int patience, int reinit) {
    timed_out = 0;
    if (reinit) random_init();
    curc = cost_eval();
    int64_t c0 = curc > 1 ? curc : 1;
    int64_t bestc = curc;
    int last = 0;
    double T0 = 0.02 * (double)c0;
    for (int t = 0; t < iters && curc > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double frac = (double)t / (double)iters;
        double temp = T0 > 0.5 ? T0 * pow(0.5 / T0, frac) : 0.5;

        double mv = rnd01();
        int kind;
        if (mv < 0.40) kind = 0;
        else if (mv < 0.60) kind = 1;
        else if (mv < 0.80) kind = 2;
        else kind = 3;
        if (kind == 1 && K < 2) kind = 0;
        if (kind == 2 && DEG < 2) kind = 0;

        int e1 = 0, e2 = 0, oldv = 0;
        if (kind == 0) {
            e1 = rndint(DEG * K);
            oldv = vol[e1];
            int nw = rndint(G);
            if (nw == oldv) continue;
            vol[e1] = nw;
        } else if (kind == 1) {
            int l = rndint(DEG), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            e1 = l * K + i1;
            e2 = l * K + i2;
            int tp = lay[e1];
            lay[e1] = lay[e2];
            lay[e2] = tp;
            fix_back(l);
        } else if (kind == 2) {
            int l1 = rndint(DEG), l2 = rndint(DEG - 1);
            if (l2 >= l1) l2++;
            int i = rndint(K);
            e1 = l1 * K + i;
            e2 = l2 * K + i;
            if (vol[e1] == vol[e2]) continue;
            int tp = vol[e1];
            vol[e1] = vol[e2];
            vol[e2] = tp;
        } else {
            e1 = rndint(DEG * K);
            oldv = vol[e1];
            int a = vol[rndint(DEG * K)], b = vol[rndint(DEG * K)];
            int bb = (rnd64() & 1) ? b : INVA[b];
            int nw = (int)TT[a * G + bb];
            if (nw == oldv) continue;
            vol[e1] = nw;
        }

        int64_t c2 = cost_eval();
        if (c2 <= curc || rnd01() < exp(-(double)(c2 - curc) / temp)) {
            curc = c2;
            if (curc < bestc) {
                bestc = curc;
                last = t;
            }
        } else {
            if (kind == 0 || kind == 3) {
                vol[e1] = oldv;
            } else if (kind == 1) {
                int tp = lay[e1];
                lay[e1] = lay[e2];
                lay[e2] = tp;
                fix_back(e1 / K);
            } else {
                int tp = vol[e1];
                vol[e1] = vol[e2];
                vol[e2] = tp;
            }
        }
    }
    return curc == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D target cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DEG > MAXDEG || DIAM < 2 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    build_cands();
    if (ncand == 0) {
        printf("0 0\n");
        return 0;
    }

    long long found = best0;
    while (elapsed() < TL) {
        if (found >= CAP) break;
        int ci = -1, KK = 1, picked = 0;
        for (int att = 0; att < 40 && !picked; att++) {
            KK = 1 + rndint(MAXK);
            long long lo = found / (2 * KK) + 1;
            int idx = 0;
            while (idx < ncand && cands[idx].order < lo) idx++;
            if (idx >= ncand) continue;
            int span = ncand - idx;
            if (span > 4) span = 4;
            int j = idx + rndint(span);
            if ((long long)2 * KK * cands[j].order > CAP) continue;
            ci = j;
            picked = 1;
        }
        if (!picked) break;
        if (!build_group(ci)) break;

        K = KK;
        N = 2 * K * G;
        if (N <= found) continue;

        int ok = run_trial(ITERS, PATIENCE, 1);
        int extra = 0;
        while (!ok && !timed_out && extra < 2 && curc <= N / 8 && elapsed() < TL) {
            ok = run_trial(ITERS, PATIENCE, 0);
            extra++;
        }
        if (ok) {
            cost_eval();
            memcpy(BESTNBR, NBR, sizeof(int) * (size_t)N * DEG);
            bestN = N;
            bestK = K;
            bestG = G;
            have_best = 1;
            found = N;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KG = bestK * bestG;
    long long m = (long long)KG * DEG;
    printf("%d %lld\n", bestN, m);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, BESTNBR[u * DEG + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as fallback start graphs.
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
# Slack extension: add vertices using spare degree; every candidate must pass
# lib.is_valid. Regular graphs have no spare degree, so this is a no-op there.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Main build: exact constructions first, then the matrix-group lift search in C,
# then slack extension. Every returned graph is checked with lib.is_valid.
#
# Timing: the C search gets the time up to time_limit - 6 s. That margin covers
# the first-time C compile, which run_c does outside the subprocess timeout.
# The subprocess timeout ends at time_limit - 2 s.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + max(1.0, time_limit - 2.0)
    c_end = start + max(1.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions. Calibration cases return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < c_end - 5.0:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: matrix-group voltage lifts, entirely in C.
    if d >= 3 and D >= 3:
        remaining = c_end - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            if cap > best_n:
                try:
                    text = lib.run_c(
                        C_SOURCE,
                        [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                        timeout=max(1.0, hard_end - time.monotonic()),
                    )
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    # Use spare degree in the best graph (no-op for regular graphs).
    if time.monotonic() < hard_end - 0.5:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, hard_end)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

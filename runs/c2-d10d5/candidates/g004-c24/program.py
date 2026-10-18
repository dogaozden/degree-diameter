import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley voltage annealing over Z_m x| Z_k2, merged from two
# variants.
#
# Vertices: A_{i,g} = i*G + g (i < K), B_{p,h} = (K+p)*G + h.
# Layer l pairs A_i with B_{lay[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Each layer is a permutation of blocks, so every vertex has degree DEG exactly.
# Reach bitmasks (uint32, up to 2K <= 16 representative blocks) check the
# diameter: left multiplication is an automorphism, so checking distances to
# block representatives suffices. Cost = unreached pairs + PEN * duplicate darts.
# Cost 0 gives a valid simple bipartite graph.
#
# Merged features:
#  - base size K in 1..8 (uint32 reach masks) with a UCB-style bandit over K;
#  - defect-targeted voltage moves (exact B-block layer lookup);
#  - near-miss intensification: a group whose trial ends with a small cost is
#    annealed further from its final state before the bandit moves on;
#  - the best stored graph is written out directly from the C side.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 8
#define PEN 1000L
#define MAXN 400000

static uint64_t rs;

static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static const int KCH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static clock_t T0;
static double TL;
static int timed_out;
static long LASTCOST;

static double elapsed(void) {
    return (double)(clock() - T0) / (double)CLOCKS_PER_SEC;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* problem parameters */
static int DEG, DIAM;

/* group Z_GM x| Z_GK, element a*GK+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM, GK, GG;
static int64_t PW[64];

/* current base state (valid for one group) */
static int K, N;
static int *LAY, *SV, *NB;
static uint32_t *RC, *RN, *TMP;
static uint32_t FULL;

/* best graph found so far */
static int *BEST_E = NULL;
static long BEST_M = 0;
static int BEST_N = 0;

static void set_group(int m, int k2, int64_t r) {
    GM = m;
    GK = k2;
    GG = m * k2;
    int64_t p = 1 % m;
    for (int t = 0; t < k2; t++) {
        PW[t] = p;
        p = p * r % m;
    }
}

static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = KCH[rndint(20)];
        int64_t m = ((int64_t)target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (gcd64(r, m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            int found = 0;
            for (int t = 0; t < 60; t++) {
                int64_t c = (m > 2) ? 2 + (int64_t)rndint((int)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = ((int64_t)a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (PW[nb] * (int64_t)a) % GM;
    t = (GM - t) % GM;
    return (int)(t * GK + nb);
}

static void free_group(void) {
    free(LAY);
    free(SV);
    free(NB);
    free(RC);
    free(RN);
    free(TMP);
    LAY = SV = NB = NULL;
    RC = RN = TMP = NULL;
}

static int alloc_group(int k, int n) {
    K = k;
    N = n;
    FULL = (uint32_t)((1ULL << (2 * k)) - 1ULL);
    LAY = malloc(sizeof(int) * (size_t)(DEG * K));
    SV = malloc(sizeof(int) * (size_t)(DEG * K));
    NB = malloc(sizeof(int) * (size_t)DEG * (size_t)N);
    RC = malloc(sizeof(uint32_t) * (size_t)N);
    RN = malloc(sizeof(uint32_t) * (size_t)N);
    TMP = malloc(sizeof(uint32_t) * (size_t)N);
    if (!LAY || !SV || !NB || !RC || !RN || !TMP) {
        free_group();
        return 0;
    }
    return 1;
}

/* Dart (l,i): A-block i to B-block lay[l*K+i] with voltage sv[l*K+i]. */
static void set_dart(int l, int i) {
    int j = LAY[l * K + i];
    int s = SV[l * K + i];
    int si = ginv(s);
    int Ab = i * GG, Bb = (K + j) * GG;
    int *nb = NB + (size_t)l * (size_t)N;
    for (int g = 0; g < GG; g++) {
        nb[Ab + g] = Bb + gmul(g, s);
        nb[Bb + g] = Ab + gmul(g, si);
    }
}

static void setup_random(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) LAY[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = LAY[l * K + i];
            LAY[l * K + i] = LAY[l * K + j];
            LAY[l * K + j] = t;
        }
    }
    for (int e = 0; e < DEG * K; e++) SV[e] = rndint(GG);
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static void compute_reach(uint32_t *out) {
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[b * GG] = 1u << b;
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = out[v];
            for (int l = 0; l < DEG; l++) x |= out[NB[(size_t)l * N + v]];
            TMP[v] = x;
            if (x != out[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(out, TMP, sizeof(uint32_t) * (size_t)N);
    }
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) {
        c += (int)(x & 1u);
        x >>= 1;
    }
    return c;
}

static long unreached(const uint32_t *r) {
    long s = 0;
    for (int v = 0; v < N; v++) s += popc(r[v]);
    return 2L * K * N - s;
}

static long dupcount(void) {
    long dup = 0;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) {
            int e = l * K + i;
            for (int l2 = 0; l2 < l; l2++) {
                int f = l2 * K + i;
                if (LAY[f] == LAY[e] && SV[f] == SV[e]) {
                    dup++;
                    break;
                }
            }
        }
    }
    return dup;
}

static long total_cost(const uint32_t *r) {
    return unreached(r) + PEN * dupcount();
}

static void store_best(void) {
    long A = (long)K * GG;
    long m = A * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    long c = 0;
    for (long u = 0; u < A; u++) {
        for (int l = 0; l < DEG; l++) {
            e[2 * c] = (int)u;
            e[2 * c + 1] = NB[(size_t)l * N + u];
            c++;
        }
    }
    free(BEST_E);
    BEST_E = e;
    BEST_M = m;
    BEST_N = N;
}

/* reinit = 1: random permutations and voltages. reinit = 0: continue from the
   current state, which is consistent because every rejected move was reverted. */
static long run_trial(int iters, int patience, int reinit) {
    int n = DEG * K;
    timed_out = 0;
    if (reinit) setup_random();

    compute_reach(RC);
    long cost = total_cost(RC);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2 = 0;
        int acc = 0;

        if (K >= 2 && rnd01() < 0.25) {
            /* layer-swap move */
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tv = LAY[e1];
            LAY[e1] = LAY[e2];
            LAY[e2] = tv;
            set_dart(l, i1);
            set_dart(l, i2);
            compute_reach(RN);
            c2 = total_cost(RN);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                acc = 1;
            } else {
                tv = LAY[e1];
                LAY[e1] = LAY[e2];
                LAY[e2] = tv;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            /* voltage move, defect-targeted with probability 0.4 */
            int l = 0, i = 0, picked = 0;
            if (rnd01() < 0.4) {
                long nbad = 0;
                for (int v = 0; v < N; v++)
                    if (RC[v] != FULL) nbad++;
                if (nbad > 0) {
                    long pick = (long)rndint((int)nbad);
                    int u = -1;
                    for (int v = 0; v < N; v++) {
                        if (RC[v] != FULL) {
                            if (pick == 0) {
                                u = v;
                                break;
                            }
                            pick--;
                        }
                    }
                    if (u >= 0) {
                        int block = u / GG;
                        l = rndint(DEG);
                        if (block < K) {
                            i = block;
                        } else {
                            i = -1;
                            for (int q = 0; q < K; q++) {
                                if (LAY[l * K + q] == block - K) {
                                    i = q;
                                    break;
                                }
                            }
                        }
                        picked = (i >= 0);
                    }
                }
            }
            if (!picked) {
                l = rndint(DEG);
                i = rndint(K);
            }
            int e = l * K + i;
            int old = SV[e];
            int nw = rndint(GG);
            if (nw == old) continue;
            SV[e] = nw;
            set_dart(l, i);
            compute_reach(RN);
            c2 = total_cost(RN);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                acc = 1;
            } else {
                SV[e] = old;
                set_dart(l, i);
            }
        }

        if (acc) {
            uint32_t *p = RC;
            RC = RN;
            RN = p;
            cost = c2;
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
            }
        }
    }
    LASTCOST = cost;
    (void)n;
    return cost;
}

static int pick_k(const long *tr, const long *wn) {
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double v = ((double)wn[k] + 1.0) / ((double)tr[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget min_n\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    long min_n = atol(argv[5]);
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    T0 = clock();

    if (DEG < 3 || DIAM < 3) {
        printf("0 0\n");
        return 0;
    }

    long tr[KMAX + 1], wn[KMAX + 1];
    for (int k = 0; k <= KMAX; k++) {
        tr[k] = 0;
        wn[k] = 0;
    }
    long found = min_n;

    while (elapsed() < TL) {
        int k = pick_k(tr, wn);
        long base = found / (2L * k);
        long span = base / 8 + 1;
        if (span < 2) span = 2;
        long target = base + 1 + (long)rndint((int)span);
        if (target < 2) target = 2;

        int gm = 0, gk = 1;
        int64_t gr = 1;
        if (!sample_group(target, &gm, &gk, &gr)) continue;
        long Nl = 2L * k * (long)gm * (long)gk;
        if (Nl <= found || Nl > MAXN) continue;

        set_group(gm, gk, gr);
        if (!alloc_group(k, (int)Nl)) break;
        tr[k] += 1;

        int ok = (run_trial(4000, 1200, 1) == 0);
        /* Near miss: keep annealing the same group from its final state. */
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (long)N / 2 && elapsed() < TL) {
            ok = (run_trial(6000, 2000, 0) == 0);
            extra++;
        }
        if (ok) {
            wn[k] += 1;
            store_best();
            found = N;
        }
        free_group();
        if (timed_out) break;
    }

    if (BEST_M == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", BEST_N, BEST_M);
    for (long c = 0; c < BEST_M; c++) {
        printf("%d %d\n", BEST_E[2 * c], BEST_E[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact baseline families.
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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
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
# Main build: exact constructions first, then the C voltage search, then slack.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search, entirely in C (group sampling, bandit, annealing).
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic()
        if c_budget > 0.5:
            timeout = max(1.0, min(c_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, int(seed) & 0x7FFFFFFF, f"{c_budget:.2f}", best_n],
                                 timeout=timeout)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

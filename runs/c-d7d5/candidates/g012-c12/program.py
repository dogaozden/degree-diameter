import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Combined search: bi-Cayley lifts over Z_m x|_r Z_k (element (a, b) coded as
# a*k + b), simulated annealing on the voltages, best-improvement polishing of
# near-misses, and reheating from the best near-miss ("elite") state.
#
# Base graph: K vertices per side, Dd layers. Layer l is a permutation P[l]
# of 0..K-1, so every vertex has degree exactly Dd. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]} for all g. Left multiplication is an
# automorphism, so BFS from one representative per fibre (2K of them) decides
# the diameter exactly.
#
# Cost = unreached (representative, vertex) pairs within DD steps
#        + PEN * (duplicate darts). Cost 0 means a valid graph.
#
# Usage: prog d D seed slice_seconds min_n
# Prints a valid graph ("n m" + edges) with n > min_n, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 3
#define GMAX 8000
#define NMAX (2 * MAXK * GMAX)
#define PEN 1000
#define POLISH_T 60
#define GPOW_MAX 64

typedef struct {
    int K, G, M, Kk, R;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[GPOW_MAX];
static double deadline = 0.0;
static int ITERS = 40000;

static int *g_adj, *g_cnt, *g_vis, *g_q;
static int g_stamp = 0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

static void load_group(Cfg *c) {
    set_group(c->M, c->Kk, c->R);
    c->G = GG;
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cost_of(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            int ba = i * G, bb = (K + j) * G;
            for (int g = 0; g < G; g++) {
                int a = ba + g, b = bb + gmul(g, s);
                g_adj[(size_t)a * Dd + g_cnt[a]++] = b;
                g_adj[(size_t)b * Dd + g_cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i]) dup++;

    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (g_stamp >= 0x7ffffff0) {
            memset(g_vis, 0, sizeof(int) * (size_t)NMAX);
            g_stamp = 0;
        }
        g_stamp++;
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                const int *au = g_adj + (size_t)u * Dd;
                for (int t = 0; t < Dd; t++) {
                    int v = au[t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return (int)unreached + PEN * dup;
}

static void swapP(Cfg *c, int l, int a, int b) {
    int t = c->P[l][a];
    c->P[l][a] = c->P[l][b];
    c->P[l][b] = t;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            swapP(c, l, i, j);
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(GG);
    }
}

static void kick(Cfg *c, int k) {
    for (int q = 0; q < k; q++) {
        int l = rint_(Dd), i = rint_(c->K);
        if (c->K >= 2 && rint_(2) == 0) {
            int i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            swapP(c, l, i, i2);
        } else {
            c->S[l][i] = rint_(GG);
        }
    }
}

/* Simulated annealing; returns the best cost seen and leaves *c in that state. */
static int anneal(Cfg *c, long iters, double T0) {
    int cost = cost_of(c);
    int bestc = cost;
    Cfg bc = *c;
    for (long t = 0; t < iters && cost != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.02;
        int l = rint_(Dd), i = rint_(c->K);
        int swapmove = (c->K >= 2 && rint_(4) == 0);
        int i2 = 0, old_s = 0;
        if (swapmove) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            swapP(c, l, i, i2);
        } else {
            old_s = c->S[l][i];
            int ns = rint_(GG);
            if (ns == old_s) continue;
            c->S[l][i] = ns;
        }
        int c2 = cost_of(c);
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                bc = *c;
            }
        } else {
            if (swapmove) swapP(c, l, i, i2);
            else c->S[l][i] = old_s;
        }
    }
    *c = bc;
    return bestc;
}

/* Best-improvement sweeps over every single voltage and every pair of targets. */
static int polish(Cfg *c) {
    int cost = cost_of(c);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K && cost != 0; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old, bestc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    int c2 = cost_of(c);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                c->S[l][i] = bestv;
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                }
            }
        }
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K && cost != 0; i++) {
                for (int i2 = i + 1; i2 < c->K && cost != 0; i2++) {
                    swapP(c, l, i, i2);
                    int c2 = cost_of(c);
                    if (c2 < cost) {
                        cost = c2;
                        improved = 1;
                    } else {
                        swapP(c, l, i, i2);
                    }
                }
            }
        }
    }
    return cost;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

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

static const int KF[] = {1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 28, 30, 32, 36, 40};

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *oK = k;
    *oR = r;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    Dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    g_adj = malloc(sizeof(int) * (size_t)NMAX * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)NMAX);
    g_vis = calloc((size_t)NMAX, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)NMAX);
    if (!g_adj || !g_cnt || !g_vis || !g_q) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now_s();
    deadline = t0 + tl;

    Cfg cur, best, elite;
    memset(&cur, 0, sizeof cur);
    memset(&best, 0, sizeof best);
    memset(&elite, 0, sizeof elite);
    int best_n = min_n, have = 0, have_elite = 0;
    int elite_cost = 1 << 30;

    while (now_s() < deadline) {
        int use_elite = have_elite && (2 * elite.K * elite.G > best_n) && (rint_(100) < 35);
        long iters;
        double T0;
        if (use_elite) {
            cur = elite;
            load_group(&cur);
            kick(&cur, 2 + rint_(Dd * cur.K / 3 + 2));
            T0 = 0.7;
            iters = ITERS / 2;
        } else {
            int K = (rint_(100) < 70) ? 1 : ((rint_(100) < 85) ? 2 : 3);
            long long g0 = (long long)best_n / (2 * K) + 1;
            long long span = g0 / 20 + 4;
            long long g = g0 + (long long)rint_((int)span);
            int M, Kk, R;
            sample_group(g, &M, &Kk, &R);
            memset(&cur, 0, sizeof cur);
            cur.K = K;
            cur.M = M;
            cur.Kk = Kk;
            cur.R = R;
            load_group(&cur);
            if (cur.G > GMAX) continue;
            random_cfg(&cur);
            T0 = 1.5;
            iters = ITERS;
        }

        int c = anneal(&cur, iters, T0);
        if (c > 0 && c <= POLISH_T) c = polish(&cur);
        int N = 2 * cur.K * cur.G;
        if (c == 0) {
            if (N > best_n) {
                best_n = N;
                best = cur;
                have = 1;
                have_elite = 0;
                elite_cost = 1 << 30;
            }
        } else if (N > best_n && c < elite_cost) {
            elite = cur;
            elite_cost = c;
            have_elite = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    load_group(&best);
    int K = best.K, G = best.G;
    int N = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best.P[l][i], s = best.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions.
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
# Greedy spare-degree extension (no-op for regular graphs).
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if time.monotonic() >= deadline:
                break
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C, seeded with the best known order as a lower bound.
    if d >= 2 and D >= 3 and time.monotonic() < deadline:
        c_slice = deadline - time.monotonic() - 1.5
        if c_slice >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_slice:.2f}", best[0]],
                                timeout=c_slice + 8.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    # Spare-degree extension (only helps non-regular graphs).
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

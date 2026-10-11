import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing on bipartite Cayley-type (Haar) graphs over
# semidirect products G = Z_M x| Z_K (element a*K+b, r^K = 1 mod M).
#
# H(G, S) has parts {(g,0)} and {(g,1)}, with (x,0)~(y,1) iff x^{-1}y in S, |S| = DEG.
# Left multiplication is an automorphism, so the graph is vertex-transitive on each
# side. It has diameter <= DIAM iff the ball of radius DIAM around (e,0) covers
# everything and the ball around (e,1) covers side 1. Cost = number of unreached
# vertices from those two sources. S always contains the identity.
# Output: "OK s_0 ... s_{DEG-1}" or "FAIL cost".
# ----------------------------------------------------------------------------

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 4096
#define MAXD 64
#define MAXK 64

static int M, K, DEG, DIAM, G;
static int RP[MAXK];
static int S[MAXD], Sinv[MAXD];
static char inS[MAXG];
static int distv[2 * MAXG];
static int qu[2 * MAXG];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    int aa = (a + RP[b] * c) % M;
    return aa * K + (b + e) % K;
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int t = (RP[nb] * a) % M;
    return ((M - t) % M) * K + nb;
}

static int cost_from(int src) {
    int V = 2 * G;
    int h = 0, t = 0;
    for (int i = 0; i < V; i++) distv[i] = -1;
    qu[t++] = src;
    distv[src] = 0;
    while (h < t) {
        int v = qu[h++];
        int dv = distv[v];
        if (dv >= DIAM) continue;
        if (v < G) {
            for (int i = 0; i < DEG; i++) {
                int u = G + gmul(v, S[i]);
                if (distv[u] < 0) {
                    distv[u] = dv + 1;
                    qu[t++] = u;
                }
            }
        } else {
            int g = v - G;
            for (int i = 0; i < DEG; i++) {
                int u = gmul(g, Sinv[i]);
                if (distv[u] < 0) {
                    distv[u] = dv + 1;
                    qu[t++] = u;
                }
            }
        }
    }
    return V - t;
}

static int total_cost(void) { return cost_from(0) + cost_from(G); }

static void set_random_S(void) {
    for (int i = 0; i < G; i++) inS[i] = 0;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < DEG; i++) {
        int x;
        do {
            x = rnd(G);
        } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    for (int i = 0; i < DEG; i++) Sinv[i] = ginv(S[i]);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("FAIL 0\n");
        return 0;
    }
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    int r = atoi(argv[3]);
    DEG = atoi(argv[4]);
    DIAM = atoi(argv[5]);
    unsigned long long seed = strtoull(argv[6], NULL, 10);
    double tl = atof(argv[7]);
    long stallLim = 20000;
    if (argc >= 9) stallLim = atol(argv[8]);
    if (M < 2 || K < 1 || K > MAXK || M * K > MAXG || DEG < 2 || DEG > MAXD ||
        DEG >= M * K || DIAM < 1 || tl <= 0) {
        printf("FAIL 0\n");
        return 0;
    }
    G = M * K;
    RP[0] = 1 % M;
    for (int b = 1; b < K; b++) RP[b] = (int)(((long long)RP[b - 1] * r) % M);
    if (((long long)RP[K - 1] * r) % M != 1 % M) {
        printf("FAIL 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    set_random_S();
    int cur = total_cost();
    int bestc = cur;
    double c0 = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    long stall = 0, it = 0;
    while (cur > 0) {
        if ((it & 63) == 0) {
            frac = ((double)clock() / CLOCKS_PER_SEC - c0) / tl;
            if (frac >= 1.0) break;
        }
        it++;
        if (stall > stallLim) {
            set_random_S();
            cur = total_cost();
            bestc = cur;
            stall = 0;
            continue;
        }
        int i = 1 + rnd(DEG - 1);
        int x = rnd(G);
        if (inS[x]) {
            stall++;
            continue;
        }
        int old = S[i];
        inS[old] = 0;
        inS[x] = 1;
        S[i] = x;
        Sinv[i] = ginv(x);
        int c2 = total_cost();
        double T = 0.5 + 2.0 * (1.0 - frac);
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[i] = old;
            Sinv[i] = ginv(old);
        }
        if (cur < bestc) {
            bestc = cur;
            stall = 0;
        } else {
            stall++;
        }
    }
    if (cur == 0) {
        printf("OK");
        for (int i = 0; i < DEG; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("FAIL %d\n", cur);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: simulated annealing on a general bipartite graph, used to polish
# a valid start graph. Moves: swap and relocate. Cost = bad vertex pairs.
# Whenever cost is 0 the state is saved and grown by one vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define LOGMAX 1024

static int DEG, DIAM;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestNv;
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static uint64_t rs = 1;
static int defi[MAXN], fulli[MAXN], stk[MAXN];
static int logOp[LOGMAX], logA[LOGMAX], logB[LOGMAX], logN;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += nv - cnt;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void raw_del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void raw_add(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void raw_remove(int a, int b) {
    raw_del_half(a, b);
    raw_del_half(b, a);
}

static void log_push(int op, int a, int b) {
    if (logN < LOGMAX) {
        logOp[logN] = op;
        logA[logN] = a;
        logB[logN] = b;
        logN++;
    }
}

static void edit_remove(int a, int b) {
    raw_remove(a, b);
    log_push(0, a, b);
}

static void edit_add(int a, int b) {
    raw_add(a, b);
    log_push(1, a, b);
}

static void undo_log(void) {
    for (int i = logN - 1; i >= 0; i--) {
        if (logOp[i] == 0) raw_add(logA[i], logB[i]);
        else raw_remove(logA[i], logB[i]);
    }
    logN = 0;
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static int swap_move(void) {
    int a = rnd(nv);
    if (deg[a] == 0) return 0;
    int c = -1;
    for (int t = 0; t < 200; t++) {
        int x = rnd(nv);
        if (x != a && col[x] == col[a] && deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int b = adjv[a][rnd(deg[a])];
    int e = adjv[c][rnd(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    logN = 0;
    edit_remove(a, b);
    edit_remove(c, e);
    edit_add(a, e);
    edit_add(c, b);
    return 1;
}

static int relocate_move(void) {
    int v = rnd(nv);
    int c = col[v];
    logN = 0;
    while (deg[v] > 0) edit_remove(v, adjv[v][deg[v] - 1]);
    int nd = 0, nf = 0;
    for (int w = 0; w < nv; w++) {
        if (w == v || col[w] == c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        edit_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        edit_remove(w, x);
        edit_add(v, w);
        k++;
    }
    return 1;
}

static void grow(void) {
    int c = rnd(2);
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    int nd = 0, nf = 0;
    for (int w = 0; w < v; w++) {
        if (col[w] != 1 - c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        raw_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        raw_remove(w, x);
        raw_add(v, w);
        k++;
    }
}

static void save_best(void) {
    memcpy(bestAdj, adjv, sizeof adjv);
    memcpy(bestDeg, deg, sizeof deg);
    memcpy(bestCol, col, sizeof col);
    bestNv = nv;
}

static void restore_best(void) {
    memcpy(adjv, bestAdj, sizeof adjv);
    memcpy(deg, bestDeg, sizeof deg);
    memcpy(col, bestCol, sizeof col);
    nv = bestNv;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [stall]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long stallLim = 1500;
    if (argc >= 6) stallLim = atol(argv[5]);
    if (stallLim < 50) stallLim = 50;
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) { deg[i] = 0; col[i] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        raw_add(u, v);
    }
    if (nv == 0) {
        printf("0 0\n");
        return 0;
    }

    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    long long cur_cost = eval_cost();
    save_best();
    int have_valid = (cur_cost == 0);
    double tstart = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;
    logN = 0;

    while (1) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
        if (frac >= 1.0) break;

        if (cur_cost == 0) {
            if (nv > bestNv || !have_valid) {
                save_best();
                have_valid = 1;
            }
            if (nv + 1 >= MAXN) break;
            grow();
            cur_cost = eval_cost();
            stall = 0;
            continue;
        }

        double T = 0.12 + 0.5 * (1.0 - frac);
        int ok = (rnd01() < 0.6) ? swap_move() : relocate_move();
        if (!ok) {
            logN = 0;
            continue;
        }
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur_cost);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur_cost = c2;
            logN = 0;
        } else {
            undo_log();
        }

        if (++stall > stallLim) {
            restore_best();
            logN = 0;
            for (int k = 0; k < 2; k++) relocate_move();
            logN = 0;
            cur_cost = eval_cost();
            stall = 0;
        }
    }

    if (cur_cost == 0 && (nv > bestNv || !have_valid)) save_best();

    long long em = 0;
    for (int v = 0; v < bestNv; v++) em += bestDeg[v];
    printf("%d %lld\n", bestNv, em / 2);
    for (int v = 0; v < bestNv; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: Cayley/Haar construction search, with fallbacks.
# ----------------------------------------------------------------------------

def _haar_candidates(G, rng):
    """(m, k, r) with G = m * k: Z_m x| Z_k (r = 1 gives the direct product) and some twisted r."""
    out = []
    for k in range(1, 41):
        if G % k or G // k < 2:
            continue
        m = G // k
        out.append((m, k, 1))
        if k == 1:
            continue
        twisted = [r for r in range(2, m)
                   if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(twisted)
        out.extend((m, k, r) for r in twisted[:2])
    rng.shuffle(out)
    return out


def _haar_group_graph(m, k, r, S):
    """Bipartite Cayley graph H(G, S): (x,0) ~ (x*s,1), with G = semidirect(m, k, r)."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
    return 2 * order, edges


def _run_haar_c(m, k, r, d, D, seed, budget):
    """Run the Haar search C engine; return the list S (length d) or None."""
    out = lib.run_c(HAAR_C, [m, k, r, d, D, seed, f"{budget:.2f}", 20000],
                    timeout=budget + 3.0)
    tok = out.split()
    if not tok or tok[0] != "OK":
        return None
    S = [int(x) for x in tok[1:1 + d]]
    return S if len(S) == d else None


def _bold_phase(d, D, G_lo, G_hi, rng, deadline, consider):
    """Climb the group order G upward, finding a valid H(G, S) of diameter <= D for each G."""
    G = G_lo
    while G <= G_hi:
        now = time.monotonic()
        if now >= deadline:
            return
        per_call = max(1.0, min(4.0, 0.12 * (deadline - now)))
        found = False
        for (m, k, r) in _haar_candidates(G, rng)[:3]:
            left = deadline - time.monotonic()
            if left < 0.3:
                return
            budget = min(per_call, left)
            try:
                S = _run_haar_c(m, k, r, d, D, rng.randrange(1 << 30), budget)
            except RuntimeError:
                return
            if S is None:
                continue
            try:
                n, e = _haar_group_graph(m, k, r, S)
            except ValueError:
                continue
            consider(n, e)
            found = True
            break
        if not found:
            return
        G += 1


# ----------------------------------------------------------------------------
# Quadrangle fallback (D = 4): incidence graph of W(q), then saturation.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _run_c(d, D, seed, graph, budget, stall=1500):
    """Run the C annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _search_all(d, D, seed, start, tl, box):
    """Bold Haar phase, then fallback and polish. box[0] always holds the best valid graph."""
    rng = random.Random(seed)

    def consider(n, e):
        if n > box[0][0] and lib.is_valid(n, e, d, D):
            box[0] = (n, e)

    G_hi = max(d + 1, lib.moore_bound(d, D) // 2)
    G_lo = max(box[0][0] // 2 + 1, d + 1, int(0.75 * G_hi))
    _bold_phase(d, D, G_lo, G_hi, rng, start + 0.55 * tl, consider)

    # Bold phase found nothing useful: fall back to the quadrangle for D = 4.
    if D == 4 and box[0][0] <= 2 * d:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Polish the best valid graph with the general annealer, which can also grow it.
    end = start + 0.93 * tl - 1.5
    remaining = end - time.monotonic()
    if remaining > 2.0:
        try:
            n2, e2 = _run_c(d, D, seed, box[0], remaining)
            consider(n2, e2)
        except Exception:
            pass


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    box = [lib.haar_graph(d, range(d))]
    if d < 3 or D < 2:
        return box[0]

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    try:
        _search_all(d, D, seed, start, tl, box)
    except Exception:
        pass  # the box keeps the best graph found so far

    best = box[0]
    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best

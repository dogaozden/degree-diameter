import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: fixed-order tabu repair with growth.
#
# Each iteration samples KCAND candidate 2-switches (targeted or random, both
# preserve degrees and bipartiteness), evaluates each by a full bitset
# all-pairs count of pairs at distance > DIAM, and applies the best candidate
# even if it is worse than the current state. Removed edges become tabu for
# re-insertion for TENURE iterations; a tabu move is allowed only if it beats
# the best cost seen in the current phase (aspiration).
#
# Whenever the cost reaches 0 the graph is saved and grown by one vertex.
# After STALL non-improving iterations the search restores the best valid
# graph, grows it, and applies three random kicks.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 24
#define TBITS 20
#define TSIZE (1 << TBITS)
#define KCAND 4
#define TENURE 12
#define LOGMAX 64

static int DEG, DIAM;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestNv;
static int have_best;
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static uint64_t rs = 1;
static int stampArr[MAXN], distArr[MAXN], qbuf[MAXN];
static int stampCur;
static int defi[MAXN], fulli[MAXN];
static uint64_t tkey[TSIZE];
static long long tuntil[TSIZE];
static long long iter;
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

static uint64_t ekey(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    return (uint64_t)a * 4096ULL + (uint64_t)b + 1ULL;
}

static size_t thash(uint64_t k) {
    return (size_t)((k * 0x9E3779B97F4A7C15ULL) >> (64 - TBITS));
}

static void tabu_set(int a, int b, long long until) {
    uint64_t k = ekey(a, b);
    size_t h = thash(k);
    for (int p = 0; p < 16; p++) {
        size_t i = (h + (size_t)p) & (TSIZE - 1);
        if (tkey[i] == 0 || tkey[i] == k) {
            tkey[i] = k;
            tuntil[i] = until;
            return;
        }
    }
    tkey[h] = k;
    tuntil[h] = until;
}

static int is_tabu(int a, int b) {
    uint64_t k = ekey(a, b);
    size_t h = thash(k);
    for (int p = 0; p < 16; p++) {
        size_t i = (h + (size_t)p) & (TSIZE - 1);
        if (tkey[i] == 0) return 0;
        if (tkey[i] == k) return tuntil[i] > iter;
    }
    return 0;
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

/* A 2-switch: remove p-q and r-s, add p-s and r-q. p, r share a colour. */
static void apply_move(const int *P) {
    int p = P[0], q = P[1], r = P[2], s = P[3];
    edit_remove(p, q);
    edit_remove(r, s);
    edit_add(p, s);
    edit_add(r, q);
}

static int make_move(int p, int r, int *P) {
    if (p == r || deg[p] == 0 || deg[r] == 0) return 0;
    if (col[p] != col[r]) return 0;
    int q = adjv[p][rnd(deg[p])];
    int s = adjv[r][rnd(deg[r])];
    if (q == s) return 0;
    if (has_edge(p, s) || has_edge(r, q)) return 0;
    P[0] = p;
    P[1] = q;
    P[2] = r;
    P[3] = s;
    return 1;
}

static int gen_targeted(int *P) {
    int v = rnd(nv);
    if (deg[v] == 0) return 0;
    stampCur++;
    int qh = 0, qt = 0;
    qbuf[qt++] = v;
    stampArr[v] = stampCur;
    distArr[v] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        if (distArr[u] >= DIAM) continue;
        for (int i = 0; i < deg[u]; i++) {
            int x = adjv[u][i];
            if (stampArr[x] != stampCur) {
                stampArr[x] = stampCur;
                distArr[x] = distArr[u] + 1;
                qbuf[qt++] = x;
            }
        }
    }
    int cnt = 0, w = -1;
    for (int x = 0; x < nv; x++) {
        if (col[x] != col[v] || deg[x] == 0 || stampArr[x] == stampCur) continue;
        cnt++;
        if (rnd(cnt) == 0) w = x;
    }
    if (w < 0) return 0;
    return make_move(v, w, P);
}

static int gen_swap(int *P) {
    int p = rnd(nv);
    if (deg[p] == 0) return 0;
    int r = -1;
    for (int t = 0; t < 50; t++) {
        int x = rnd(nv);
        if (x != p && col[x] == col[p] && deg[x] > 0) { r = x; break; }
    }
    if (r < 0) return 0;
    return make_move(p, r, P);
}

static int gen_candidate(int *P) {
    if (rnd01() < 0.7) return gen_targeted(P);
    return gen_swap(P);
}

/* Add a vertex: join it to up to DEG opposite-side vertices, taking spare
   degree first and stealing an edge from a full vertex otherwise. */
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
    for (int i = nd - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = defi[i]; defi[i] = defi[j]; defi[j] = t;
    }
    for (int i = nf - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = fulli[i]; fulli[i] = fulli[j]; fulli[j] = t;
    }
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
    have_best = 1;
}

static void restore_best(void) {
    memcpy(adjv, bestAdj, sizeof adjv);
    memcpy(deg, bestDeg, sizeof deg);
    memcpy(col, bestCol, sizeof col);
    nv = bestNv;
    logN = 0;
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
    long stall = 400;
    if (argc >= 6) stall = atol(argv[5]);
    if (stall < 20) stall = 20;
    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX - 1 || DIAM < 1 || tl <= 0) {
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
        int *stk = qbuf;
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

    bestNv = 0;
    have_best = 0;
    stampCur = 0;
    iter = 0;
    logN = 0;

    long long cur = eval_cost();
    long long phaseBest = cur;
    long sinceImp = 0;
    if (cur == 0) save_best();

    double t0 = (double)clock() / CLOCKS_PER_SEC;

    while (1) {
        double el = (double)clock() / CLOCKS_PER_SEC - t0;
        if (el >= tl) break;

        if (cur == 0) {
            if (!have_best || nv > bestNv) save_best();
            if (nv + 2 >= MAXN) break;
            grow();
            cur = eval_cost();
            phaseBest = cur;
            sinceImp = 0;
            continue;
        }

        if (sinceImp > stall) {
            if (have_best) {
                restore_best();
                if (nv + 2 >= MAXN) break;
                grow();
            }
            for (int k = 0; k < 3; k++) {
                int P[4];
                if (gen_candidate(P)) {
                    logN = 0;
                    apply_move(P);
                }
            }
            logN = 0;
            cur = eval_cost();
            phaseBest = cur;
            sinceImp = 0;
            continue;
        }

        int found = 0;
        int bestP[4];
        long long bestC = 0;
        for (int k = 0; k < KCAND; k++) {
            int P[4];
            if (!gen_candidate(P)) continue;
            logN = 0;
            apply_move(P);
            long long c = eval_cost();
            undo_log();
            int tb = is_tabu(P[0], P[3]) || is_tabu(P[2], P[1]);
            if (tb && c >= phaseBest) continue;
            if (!found || c < bestC || (c == bestC && rnd(2) == 0)) {
                found = 1;
                bestC = c;
                memcpy(bestP, P, sizeof bestP);
            }
        }
        iter++;
        if (found) {
            logN = 0;
            apply_move(bestP);
            tabu_set(bestP[0], bestP[1], iter + TENURE);
            tabu_set(bestP[2], bestP[3], iter + TENURE);
            logN = 0;
            cur = bestC;
            if (cur < phaseBest) {
                phaseBest = cur;
                sinceImp = 0;
            } else {
                sinceImp++;
            }
        } else {
            sinceImp++;
        }
    }

    if (cur == 0 && (!have_best || nv > bestNv)) save_best();

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
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
# Python constructions and glue.
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
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


def _run_c(d, D, seed, graph, budget, stall=400):
    """Run the tabu engine from `graph` for `budget` seconds and parse the result."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        # Ties go to the later candidate, so saturated starts beat plain ones.
        nonlocal best
        if n >= best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Starting constructions (kept valid by is_valid).
    if D == 3:
        for q in [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]:
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Main phase: tabu repair with growth, started from the best construction.
    end = t_start + 0.92 * tl - 2.0
    budget = end - time.monotonic() - 1.5
    if budget >= 2.0:
        try:
            n2, e2 = _run_c(d, D, seed, best, budget)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

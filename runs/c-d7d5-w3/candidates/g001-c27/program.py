import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d (order 2(q^2+q+1), diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Cyclic start: Haar graphs H(Z_m, S) with |S| = d (bipartite, d-regular).
# Grow m while a random shift set still gives diameter <= D.
# ----------------------------------------------------------------------------

def _cyclic_start(d, D, seed, until):
    rng = random.Random(1000003 * seed + 17 * d + D)
    best = None
    m = 2 * d
    cap = max(2 * d, lib.moore_bound(d, D) // 4)
    while m <= cap and time.monotonic() < until:
        found = None
        for _ in range(10):
            if time.monotonic() >= until:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, e = lib.haar_graph(m, S)
            if lib.within_diameter(n, e, D):
                found = (n, e)
                break
        if found is None:
            break
        best = found
        m += max(1, m // 25)
    return best


# ----------------------------------------------------------------------------
# C engine: grow-and-repair search on general bipartite graphs.
#
# State: bipartite graph, max degree d, colour 0 / colour 1 sides.
# Growth: add an (A, B) pair and split random old edges (x,y) into (x,b), (a,y),
#         which keeps all old degrees fixed.
# Repair: simulated annealing with degree-preserving 2-switches and
#         edge additions between unsaturated vertices. Cost = number of
#         unordered vertex pairs at distance > D (bitset BFS).
# Keeps the best valid graph; on stall it restores the best and retries growth.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2800
#define MAXW 44
#define MAXDEG 64
#define MAXE 200000
#define STALL 4000
#define TEMP 0.6

static int Dd = 3, DD = 3;
static int N = 0;
static int col[MAXN];
static unsigned char adjm[MAXN][MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static int eu[MAXE], ev[MAXE];
static int ne = 0;
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static int bestN = 0, bestm = 0;
static int bu[MAXE], bv[MAXE];
static double deadline = 0.0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void clear_state(void) {
    memset(adjm, 0, sizeof(adjm));
    memset(deg, 0, sizeof(deg));
    ne = 0;
}

static void rem_list(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
}

static void add_e(int u, int v) {
    if (col[u] == 1) { int t = u; u = v; v = t; }
    eu[ne] = u;
    ev[ne] = v;
    ne++;
    adjm[u][v] = adjm[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_e(int u, int v) {
    for (int i = 0; i < ne; i++)
        if ((eu[i] == u && ev[i] == v) || (eu[i] == v && ev[i] == u)) {
            ne--;
            eu[i] = eu[ne];
            ev[i] = ev[ne];
            break;
        }
    adjm[u][v] = adjm[v][u] = 0;
    rem_list(u, v);
    rem_list(v, u);
}

/* Number of unordered pairs at distance > DD. */
static long cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *x = cur + (size_t)nb[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= x[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long un = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[(size_t)v * W + w]);
        un += N - c;
    }
    return un / 2;
}

static int grow1(void) {
    if (N + 2 > MAXN || ne == 0) return 0;
    int oldN = N, a = N, b = N + 1;
    col[a] = 0;
    col[b] = 1;
    deg[a] = deg[b] = 0;
    N += 2;
    add_e(a, b);
    for (int t = 0; t < 200000 && deg[a] < Dd && deg[b] < Dd && ne > 0; t++) {
        int i = rint_(ne);
        int x = eu[i], y = ev[i];
        if (x >= oldN || y >= oldN) continue;
        if (adjm[x][b] || adjm[a][y]) continue;
        del_e(x, y);
        add_e(x, b);
        add_e(a, y);
    }
    return 1;
}

static void save_best(void) {
    bestN = N;
    bestm = ne;
    memcpy(bu, eu, sizeof(int) * (size_t)ne);
    memcpy(bv, ev, sizeof(int) * (size_t)ne);
}

static void restore_best(void) {
    clear_state();
    N = bestN;
    for (int i = 0; i < bestm; i++) add_e(bu[i], bv[i]);
}

/* Annealing repair. Returns 0 on success, positive cost on stall, -1 on timeout. */
static long attempt(void) {
    long cur = cost();
    long bestc = cur;
    long stall = 0;
    long it = 0;
    while (cur > 0) {
        if ((it & 31) == 0 && now_s() > deadline) return -1;
        it++;
        int kind = (rint_(4) == 0);   /* 1 = add edge, 0 = swap */
        int a1 = 0, b1 = 0, a2 = 0, b2 = 0, applied = 0;
        if (kind) {
            for (int t = 0; t < 60 && !applied; t++) {
                int a = rint_(N), b = rint_(N);
                if (col[a] != 0 || col[b] != 1) continue;
                if (deg[a] >= Dd || deg[b] >= Dd || adjm[a][b]) continue;
                add_e(a, b);
                a1 = a;
                b1 = b;
                applied = 1;
            }
        } else if (ne >= 2) {
            int i = rint_(ne), j = rint_(ne);
            if (i != j) {
                a1 = eu[i]; b1 = ev[i]; a2 = eu[j]; b2 = ev[j];
                if (a1 != a2 && b1 != b2 && !adjm[a1][b2] && !adjm[a2][b1]) {
                    del_e(a1, b1);
                    del_e(a2, b2);
                    add_e(a1, b2);
                    add_e(a2, b1);
                    applied = 1;
                }
            }
        }
        if (!applied) continue;
        long nc = cost();
        int accept = (nc <= cur) || (urand() < exp(-(double)(nc - cur) / TEMP));
        if (accept) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                stall = 0;
            } else {
                stall++;
            }
        } else {
            if (kind) {
                del_e(a1, b1);
            } else {
                del_e(a1, b2);
                del_e(a2, b1);
                add_e(a1, b1);
                add_e(a2, b2);
            }
            stall++;
        }
        if (stall > STALL) return cur;
    }
    return 0;
}

static int read_start(int n, int m) {
    static int tu[MAXE], tv[MAXE];
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &tu[i], &tv[i]) != 2) return 0;
    for (int i = 0; i < m; i++)
        if (tu[i] < 0 || tu[i] >= n || tv[i] < 0 || tv[i] >= n || tu[i] == tv[i]) return 0;
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int ch = 1;
        while (ch) {
            ch = 0;
            for (int i = 0; i < m; i++) {
                if (col[tu[i]] >= 0 && col[tv[i]] < 0) { col[tv[i]] = 1 - col[tu[i]]; ch = 1; }
                else if (col[tv[i]] >= 0 && col[tu[i]] < 0) { col[tu[i]] = 1 - col[tv[i]]; ch = 1; }
            }
        }
    }
    for (int i = 0; i < m; i++)
        if (col[tu[i]] == col[tv[i]]) return 0;
    clear_state();
    N = n;
    for (int i = 0; i < m; i++) {
        int u = tu[i], v = tv[i];
        if (adjm[u][v] || deg[u] >= Dd || deg[v] >= Dd) {
            clear_state();
            return 0;
        }
        add_e(u, v);
    }
    return 1;
}

static void build_complete(void) {
    clear_state();
    N = 2 * Dd;
    for (int i = 0; i < Dd; i++) col[i] = 0;
    for (int i = Dd; i < 2 * Dd; i++) col[i] = 1;
    for (int i = 0; i < Dd; i++)
        for (int j = Dd; j < 2 * Dd; j++) add_e(i, j);
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    if (Dd < 1 || Dd > MAXDEG || DD < 1 || 2 * Dd + 2 > MAXN) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    deadline = now_s() + tl;

    int n = 0, m = 0, ok = 0;
    if (scanf("%d %d", &n, &m) == 2 && n > 0 && n <= MAXN - 2 && m >= 0 && m <= MAXE)
        ok = read_start(n, m);
    if (!ok) build_complete();

    int have = 0;
    if (cost() == 0) {
        save_best();
        have = 1;
    } else {
        build_complete();
        if (cost() == 0) {
            save_best();
            have = 1;
        }
    }

    if (have) {
        int chunk = 1;
        while (now_s() < deadline) {
            int good = 1;
            for (int k = 0; k < chunk; k++)
                if (!grow1()) { good = 0; break; }
            if (!good) break;
            long r = attempt();
            if (r < 0) break;
            if (r == 0) {
                save_best();
                if (chunk < 32) chunk *= 2;
            } else {
                restore_best();
                if (chunk > 1) chunk /= 2;
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestm);
    for (int i = 0; i < bestm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact baseline, cyclic start, C grow-and-repair, safe fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(3.0, min(0.85 * time_limit, time_limit - 6.0))
    end = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3 and time.monotonic() < end - 3.0:
        start = _cyclic_start(d, D, seed, t0 + 0.2 * budget)
        if start is None or start[0] < best[0]:
            start = best
        c_budget = end - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                                stdin_graph=start, timeout=time_limit - 3.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

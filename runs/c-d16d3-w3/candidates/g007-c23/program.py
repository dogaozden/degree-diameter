"""Combined diameter-3 search: multiset arc extensions, then C augmentation engines.

Pipeline:
  1. Structured starts, all checked with lib.is_valid: projective plane / Araujo-Pardo-Lopez
     (known_start), conic blow-up, W(q) for D >= 4, and K_{d,d} as the always-valid fallback.
  2. C_MULTI (new): for a bipartite base graph, add copies of side-0 vertices (joined to their
     neighbourhoods) and copies of side-1 vertices, as MULTISETS. Repeats are allowed, so each
     copy is a twin. Load on every base vertex stays <= d - deg. The annealer maximises the
     number of copies. The output is checked for diameter <= D in C. For PG(2,q) with d = q+1+s
     this lifts the record conic/arc sets (14 per side at d = 16) toward about 26 per side.
  3. C_ADD (vertex-addition engine) and C_SQUEEZE (annealed swaps plus semidirect voltage lifts)
     run on the best graph. Both were carried over from the parent programs.

Every candidate passes lib.is_valid before it can replace the best, so a broken engine only
wastes time.
"""
import itertools
import random
import time

import lib

C_MULTI = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MN 2048
#define MDG 64
#define MW (MN / 64)
#define LOGN 4096
#define CYC 200000

static int n0, dd, DD;
static int bdeg[MN], bnb[MN][MDG], bside[MN], cap[MN];
static int cnt[MN], load[MN], bestcnt[MN], res[2][MN];
static int cand[MN], ncand;
static int opv[LOGN], ops[LOGN], nlog;
static int size_cur, best_size;
static int edeg[MN], eadj[MN][MDG];
static uint64_t rs = 88172645463325252ULL;
static uint64_t R1[MN][MW], R2[MN][MW];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Add (sg=+1) or remove (sg=-1) one copy of candidate v; loads follow its neighbours. */
static void apply_op(int v, int sg) {
    if (nlog < LOGN) {
        opv[nlog] = v;
        ops[nlog] = sg;
        nlog++;
    }
    cnt[v] += sg;
    size_cur += sg;
    for (int k = 0; k < bdeg[v]; k++) load[bnb[v][k]] += sg;
}

static void undo_all(void) {
    for (int i = nlog - 1; i >= 0; i--) {
        int v = opv[i], sg = ops[i];
        cnt[v] -= sg;
        size_cur -= sg;
        for (int k = 0; k < bdeg[v]; k++) load[bnb[v][k]] -= sg;
    }
    nlog = 0;
}

/* Greedily add every candidate that fits, in random cyclic order. */
static void fill_sweep(void) {
    if (ncand == 0) return;
    int start = rndint(ncand);
    nlog = 0;
    for (int t = 0; t < ncand; t++) {
        int v = cand[(start + t) % ncand];
        int ok = 1;
        for (int k = 0; k < bdeg[v]; k++) {
            int u = bnb[v][k];
            if (load[u] >= cap[u]) { ok = 0; break; }
        }
        if (ok) apply_op(v, 1);
    }
    nlog = 0;
}

/* Annealed ruin-and-recreate over multisets of candidates. Maximises the total multiplicity. */
static void anneal(double until) {
    if (ncand == 0) {
        best_size = 0;
        memset(bestcnt, 0, sizeof(bestcnt));
        return;
    }
    size_cur = 0;
    nlog = 0;
    fill_sweep();
    best_size = size_cur;
    memcpy(bestcnt, cnt, sizeof(int) * n0);
    long it = 0;
    for (;;) {
        if ((it & 255) == 0 && now() > until) break;
        it++;
        double frac = (double)(it % CYC) / CYC;
        double T = 0.5 * pow(0.1, frac);
        int v = cand[rndint(ncand)];
        int old = size_cur;
        nlog = 0;
        apply_op(v, 1);
        int fail = 0;
        for (;;) {
            int bad = -1;
            for (int k = 0; k < bdeg[v]; k++) {
                int u = bnb[v][k];
                if (load[u] > cap[u]) { bad = u; break; }
            }
            if (bad < 0) break;
            int pick = -1, seen = 0;
            for (int k = 0; k < bdeg[bad]; k++) {
                int x = bnb[bad][k];
                if (cnt[x] > 0) {
                    seen++;
                    if (rndint(seen) == 0) pick = x;
                }
            }
            if (pick < 0 || nlog > LOGN - 128) { fail = 1; break; }
            apply_op(pick, -1);
        }
        if (fail) {
            undo_all();
            continue;
        }
        int delta = size_cur - old;
        if (delta < 0 && rnd01() >= exp(delta / T)) undo_all();
        nlog = 0;
        if (it % 64 == 0) fill_sweep();
        if (size_cur > best_size) {
            best_size = size_cur;
            memcpy(bestcnt, cnt, sizeof(int) * n0);
        }
    }
}

static void print_adj(int N, const int *deg, int adj[][MDG]) {
    long m = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) m++;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

/* Bitset ball-growth: every vertex must reach all N vertices within DD steps. */
static int diam_ok(int N, const int *deg, int adj[][MDG], int D_) {
    if (N > MN) return 0;
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) R1[v][w] = 0;
        R1[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) R2[v][w] = R1[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) R2[v][w] |= R1[u][w];
            }
        }
        memcpy(R1, R2, sizeof(R1));
    }
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(R1[v][w]);
        if (c != N) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    double t0 = now(), t_end = t0 + budget * 0.9;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MN / 2 || dd < 1 || dd > MDG || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    n0 = n;
    for (int v = 0; v < n0; v++) bdeg[v] = 0;
    int bad = 0;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || bdeg[u] >= MDG || bdeg[v] >= MDG) {
            bad = 1;
            break;
        }
        bnb[u][bdeg[u]++] = v;
        bnb[v][bdeg[v]++] = u;
    }
    for (int v = 0; v < n0; v++) bside[v] = -1;
    static int queue[MN];
    for (int s = 0; s < n0 && !bad; s++) {
        if (bside[s] >= 0) continue;
        int h = 0, t = 0;
        bside[s] = 0;
        queue[t++] = s;
        while (h < t) {
            int x = queue[h++];
            for (int k = 0; k < bdeg[x]; k++) {
                int y = bnb[x][k];
                if (bside[y] < 0) {
                    bside[y] = 1 - bside[x];
                    queue[t++] = y;
                } else if (bside[y] == bside[x]) {
                    bad = 1;
                }
            }
        }
    }
    for (int v = 0; v < n0 && !bad; v++) {
        cap[v] = dd - bdeg[v];
        if (cap[v] < 0) bad = 1;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* Side cs candidates are copied; their copies load the other side, so the two runs are independent. */
    for (int cs = 0; cs < 2; cs++) {
        ncand = 0;
        for (int v = 0; v < n0; v++)
            if (bside[v] == cs && bdeg[v] > 0) cand[ncand++] = v;
        for (int v = 0; v < n0; v++) {
            cnt[v] = 0;
            load[v] = 0;
        }
        double until = t0 + (t_end - t0) * (cs + 1) / 2.0;
        anneal(until);
        for (int v = 0; v < n0; v++) res[cs][v] = (bside[v] == cs) ? bestcnt[v] : 0;
    }

    int extra = 0;
    for (int cs = 0; cs < 2; cs++)
        for (int v = 0; v < n0; v++) extra += res[cs][v];
    int N = n0 + extra;
    int ok = (extra > 0 && N <= MN);
    if (ok) {
        for (int v = 0; v < n0; v++) {
            edeg[v] = bdeg[v];
            for (int k = 0; k < bdeg[v]; k++) eadj[v][k] = bnb[v][k];
        }
        int nid = n0;
        for (int cs = 0; cs < 2 && ok; cs++) {
            for (int v = 0; v < n0 && ok; v++) {
                if (bside[v] != cs) continue;
                for (int c = 0; c < res[cs][v] && ok; c++) {
                    int id = nid++;
                    edeg[id] = 0;
                    for (int k = 0; k < bdeg[v]; k++) {
                        int u = bnb[v][k];
                        if (edeg[u] >= MDG || edeg[id] >= MDG) { ok = 0; break; }
                        eadj[id][edeg[id]++] = u;
                        eadj[u][edeg[u]++] = id;
                    }
                }
            }
        }
        for (int v = 0; v < N && ok; v++)
            if (edeg[v] > dd) ok = 0;
        if (ok) ok = diam_ok(N, edeg, eadj, DD);
    }
    if (ok) print_adj(N, edeg, eadj);
    else print_adj(n0, bdeg, bnb);
    return 0;
}
"""

C_ADD = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""

C_SQUEEZE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

typedef struct { int i, j, g; } Dart;

static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        double lift_share = had_start ? 0.05 : 0.6;
        lift_search(&best, t0 + (t_end - t0) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured starts.
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Best directly constructible graph for D = 3: projective plane or Araujo-Pardo/Lopez."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def _gq_w(q):
    """Incidence graph of W(q), the generalized quadrangle (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _two_sides(n, adj):
    """Bipartition as a list of 0/1 labels, or None if the graph is not bipartite."""
    side = [-1] * n
    for s in range(n):
        if side[s] >= 0:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if side[y] < 0:
                    side[y] = 1 - side[x]
                    stack.append(y)
                elif side[y] == side[x]:
                    return None
    return side


def _multi_estimate(d, n, edges):
    """Upper-style estimate of the order reached by multiset copies on both sides."""
    adj = lib.adjacency(n, edges)
    side = _two_sides(n, adj)
    if side is None:
        return 0
    est = n
    for cs in (0, 1):
        cand = [v for v in range(n) if side[v] == cs and adj[v]]
        other = [u for u in range(n) if side[u] != cs]
        if not cand:
            continue
        tot_cap = sum(d - len(adj[u]) for u in other)
        avg = sum(len(adj[v]) for v in cand) / len(cand)
        est += int(tot_cap / avg)
    return est


# ----------------------------------------------------------------------------
# C engine drivers.
# ----------------------------------------------------------------------------

def _run_multi(n0, e0, d, D, seed, budget):
    text = lib.run_c(C_MULTI, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def _run_add(n0, e0, d, D, seed, budget):
    text = lib.run_c(C_ADD, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def _run_squeeze(n0, e0, d, D, seed, budget):
    text = lib.run_c(C_SQUEEZE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    best = [fallback]

    def consider(g):
        try:
            if g is None:
                return False
            n, e = g
            if n > best[0][0] and lib.is_valid(n, e, d, D):
                best[0] = (n, e)
                return True
        except Exception:
            pass
        return False

    # Structured starts.
    consider(known_start(d, D))
    consider(conic_blowup(d, D))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                consider(_gq_w(q))
                break

    # Multiset arc extensions (diameter 3): C_MULTI on the top-ranked bases.
    if D >= 3:
        bases = []
        for q in range(2, min(d - 1, 23) + 1):
            if lib.is_prime_power(q):
                bases.append(lib.projective_plane_incidence(q))
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            bases.append(lib.araujo_lopez_graph(d - 2))
        ranked = sorted(((_multi_estimate(d, n, e), (n, e)) for n, e in bases),
                        key=lambda t: -t[0])
        for i, (est, (n, e)) in enumerate(ranked[:2]):
            if est <= best[0][0]:
                continue
            remaining = hard_end - time.monotonic()
            if remaining < 2.0:
                break
            budget = remaining * (0.55 if i == 0 else 0.30)
            try:
                n2, e2 = _run_multi(n, e, d, D, seed * 131 + i + 1, budget)
                consider((n2, e2))
            except Exception:
                pass

    # Vertex-addition engine from the current best.
    remaining = hard_end - time.monotonic()
    if remaining > 3.0:
        try:
            n1, e1 = _run_add(best[0][0], best[0][1], d, D, seed * 31 + 1,
                              max(0.5, 0.4 * remaining - 1.0))
            consider((n1, e1))
        except Exception:
            pass

    # Squeeze engine (annealed swaps, voltage lifts, grow-by-two) from the current best.
    remaining = hard_end - time.monotonic()
    if remaining > 3.0:
        try:
            n2, e2 = _run_squeeze(best[0][0], best[0][1], d, D, seed * 31 + 2,
                                  max(0.5, remaining - 1.5))
            consider((n2, e2))
        except Exception:
            pass

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        best[0] = fallback
    return best[0]

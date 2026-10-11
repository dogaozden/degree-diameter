"""Combined program, variant with tabu repair.

Python builds the best known start graph (Araujo-Pardo and Lopez record for d-2 a prime power,
or the projective plane for d-1 a prime power). The C engine then grows it by two vertices at a
time. Each new vertex pair is inserted randomly or greedily, then repaired by a TABU search over
degree-preserving swaps: at every step it evaluates a batch of targeted proposals exactly and
takes the best non-tabu move (aspiration allows a tabu move that beats the best seen). This
replaces the earlier annealed repair. Failed attempts are kicked (random degree-preserving swaps)
before retrying.

Construction note: no new algebraic family is added here. The change is in the search dynamics,
which is the part I could verify by reasoning. Every output is checked in C and again in Python
with lib.is_valid, so a failure costs time, not validity.
"""
import time

import lib

TIME_FRAC = 0.93  # fraction of time_limit covered by the C run plus its compile

C_SOURCE = r'''
/* Bipartite degree-diameter search core, tabu variant.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
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
#define K_CAND 24
#define TABU_LEN 64

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static uint64_t *final_reach = RA;
static int final_W = 0;

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
    final_reach = cur;
    final_W = W;
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

/* ------------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------------ groups and Haar graphs */

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

static void build_haar(Graph *g, int N, const Grp *G, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + gmul(G, x, S[i]));
}

static long haar_anneal(const Grp *G, int N, int *S, double until) {
    static Graph g;
    for (int i = 0; i < d; i++) {
        for (;;) {
            int x = rndint(N), ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == x) { ok = 0; break; }
            if (ok) { S[i] = x; break; }
        }
    }
    build_haar(&g, N, G, S);
    long bad = bad_pairs(&g);
    double T = 0.6;
    long it = 0;
    while (bad > 0) {
        if ((++it & 255) == 0 && now() > until) break;
        int i = rndint(d);
        int x = rndint(N), clash = 0;
        for (int j = 0; j < d; j++) if (S[j] == x) { clash = 1; break; }
        if (clash) continue;
        int old = S[i];
        S[i] = x;
        build_haar(&g, N, G, S);
        long nb = bad_pairs(&g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else S[i] = old;
        T *= 0.9995;
        if (T < 0.1) T = 0.6;
    }
    return bad;
}

static void haar_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    int S[MAXD];
    long moore = moore_bound();
    while (now() < until) {
        int N = best->n / 2 + 1;
        if (N < d) N = d;
        if (2L * N > moore || 2 * N > MAXN) return;
        if (rndint(3) == 0 && 2L * (N + 1) <= moore && 2 * (N + 1) <= MAXN) N++;
        if (!random_group(N, &G)) continue;
        double slice = until - now();
        if (slice > 2.0) slice = 2.0;
        long bad = haar_anneal(&G, N, S, now() + slice);
        if (bad == 0) {
            build_haar(&cand, N, &G, S);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ proposals and kicks */

/* Degree-preserving swap (v,u),(s,t) -> (v,t),(s,u), side(t) != side(v), side(s) == side(v).
 * Targeted mode reads final_reach, so it must follow a bad_pairs call on the current state. */
static int propose(const Graph *g, int v, int *pu, int *ps, int *pt, int targeted) {
    int n = g->n;
    int u, s, t;
    if (g->deg[v] == 0) return 0;
    u = g->adj[v][rndint(g->deg[v])];
    if (!targeted) {
        s = rndint(n);
        if (g->side[s] != g->side[v] || g->deg[s] == 0) return 0;
        t = g->adj[s][rndint(g->deg[s])];
    } else {
        int w = -1;
        for (int tries = 0; tries < 64; tries++) {
            int c = rndint(n);
            if (c != v && !((final_reach[(size_t)v * final_W + c / 64] >> (c % 64)) & 1ULL)) { w = c; break; }
        }
        if (w < 0) return 0;
        int L = g->side[w] == g->side[v] ? 1 : 2;
        t = w;
        for (int k = 0; k < L; k++) {
            if (g->deg[t] == 0) return 0;
            t = g->adj[t][rndint(g->deg[t])];
        }
        if (g->deg[t] == 0) return 0;
        s = g->adj[t][rndint(g->deg[t])];
    }
    if (s == v || t == u || g->side[t] == g->side[v] || g->side[s] != g->side[v]) return 0;
    if (has_edge(g, v, t) || has_edge(g, s, u)) return 0;
    *pu = u; *ps = s; *pt = t;
    return 1;
}

/* Spare-degree fill across the bipartition: never increases any distance. */
static int fill_slack(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
}

/* Iterated-local-search kick: k random degree-preserving swaps applied unconditionally. */
static void kick(Graph *g, int k) {
    for (int it = 0; it < k; it++) {
        for (int tries = 0; tries < 50; tries++) {
            int v = rndint(g->n), u, s, t;
            if (!propose(g, v, &u, &s, &t, 0)) continue;
            del_edge(g, v, u);
            del_edge(g, s, t);
            add_edge(g, v, t);
            add_edge(g, s, u);
            break;
        }
    }
}

/* ------------------------------------------------------------------ tabu repair (new) */

/* Recently removed edges are tabu to re-add for a short tenure. Aspiration: a tabu move is
 * allowed if it beats the best bad count seen in this repair. */
static long tabu_key[TABU_LEN];
static long tabu_exp[TABU_LEN];
static int tabu_pos = 0;
static long tabu_iter = 0;

static long pair_key(int a, int b) {
    return a < b ? (long)a * MAXN + b : (long)b * MAXN + a;
}

static int is_tabu(int a, int b) {
    long k = pair_key(a, b);
    for (int i = 0; i < TABU_LEN; i++)
        if (tabu_key[i] == k && tabu_exp[i] > tabu_iter) return 1;
    return 0;
}

static void push_tabu(int a, int b, int tenure) {
    tabu_key[tabu_pos] = pair_key(a, b);
    tabu_exp[tabu_pos] = tabu_iter + tenure;
    tabu_pos = (tabu_pos + 1) % TABU_LEN;
}

/* Returns 0 when valid (bad == 0), else the bad count at timeout. */
static long tabu_repair(Graph *w, double until) {
    long bad = bad_pairs(w);
    long best_bad = bad;
    int tenure = 8 + rndint(8);
    while (bad > 0) {
        if (now() > until) return bad;
        tabu_iter++;
        bad_pairs(w); /* make final_reach and badv match the current state */

        int PV[K_CAND], PU[K_CAND], PS[K_CAND], PT[K_CAND], np = 0;
        for (int c = 0; c < K_CAND; c++) {
            int v = rndint(w->n);
            for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(w->n);
            int u, s, t;
            if (!propose(w, v, &u, &s, &t, 1)) continue;
            PV[np] = v; PU[np] = u; PS[np] = s; PT[np] = t; np++;
        }
        if (np == 0) continue;

        long bn = -1;
        int bi = -1;
        for (int i = 0; i < np; i++) {
            int v = PV[i], u = PU[i], s = PS[i], t = PT[i];
            int tb = is_tabu(v, t) || is_tabu(s, u);
            del_edge(w, v, u);
            del_edge(w, s, t);
            add_edge(w, v, t);
            add_edge(w, s, u);
            long nb = bad_pairs(w);
            del_edge(w, v, t);
            del_edge(w, s, u);
            add_edge(w, v, u);
            add_edge(w, s, t);
            if (tb && nb >= best_bad) continue;
            if (bn < 0 || nb < bn || (nb == bn && rndint(2))) { bn = nb; bi = i; }
        }
        if (bi < 0) continue;

        int v = PV[bi], u = PU[bi], s = PS[bi], t = PT[bi];
        del_edge(w, v, u);
        del_edge(w, s, t);
        add_edge(w, v, t);
        add_edge(w, s, u);
        push_tabu(v, u, tenure);
        push_tabu(s, t, tenure);
        bad = bn;
        if (bad < best_bad) best_bad = bad;
        if (tabu_iter % 200 == 0) tenure = 8 + rndint(8);
    }
    return 0;
}

/* ------------------------------------------------------------------ grow by two */

static void insert_pair(const Graph *best, Graph *dst) {
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
        int b = dst->adj[a][rndint(dst->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(dst, a, b);
        add_edge(dst, x, b);
        add_edge(dst, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

static void insert_pair_greedy(const Graph *best, Graph *dst, int cand) {
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0; k < d - 1; k++) {
        int ba = -1, bb = -1;
        long bestbad = -1;
        for (int c = 0; c < cand; c++) {
            int a = rndint(n);
            if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
            int b = dst->adj[a][rndint(dst->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            del_edge(dst, a, b);
            add_edge(dst, x, b);
            add_edge(dst, y, a);
            long nb = bad_pairs(dst);
            del_edge(dst, x, b);
            del_edge(dst, y, a);
            add_edge(dst, a, b);
            if (bestbad < 0 || nb < bestbad) { bestbad = nb; ba = a; bb = b; }
        }
        if (ba < 0) break;
        del_edge(dst, ba, bb);
        add_edge(dst, x, bb);
        add_edge(dst, y, ba);
        used[ba] = used[bb] = stamp;
    }
    fill_slack(dst);
}

static void grow_search(Graph *best, double until) {
    static Graph frontier;
    int have = 0, fails = 0;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        if (!have) {
            if (fails % 2 == 0) insert_pair_greedy(best, &frontier, 40);
            else { insert_pair(best, &frontier); fill_slack(&frontier); }
            if (fails >= 2) kick(&frontier, 3 + fails % 4);
            have = 1;
        }
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 2 > 4.0 ? left / 2 : 4.0);
        long bad = tabu_repair(&frontier, now() + slice);
        if (bad == 0 && is_valid(&frontier)) {
            copy_graph(best, &frontier);
            have = 0;
            fails = 0;
        } else if (++fails >= 3) {
            have = 0;
        }
    }
}

/* ------------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    for (int i = 0; i < TABU_LEN; i++) { tabu_key[i] = -1; tabu_exp[i] = 0; }

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        if (had_start) {
            grow_search(&best, t_end);
        } else {
            double span = t_end - t0;
            haar_search(&best, t0 + span * 0.3);
            if (best.n == 0) complete_bipartite(&best);
            grow_search(&best, t_end);
        }
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    static Graph tmp;
    copy_graph(&tmp, &best);
    if (fill_slack(&tmp) > 0 && is_valid(&tmp)) copy_graph(&best, &tmp);

    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def known_start(d, D):
    """Best known construction Python builds directly for (d, D), or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)       # Moore graph, optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                return lib.araujo_lopez_graph(d - 2)           # record 2(q^2+q+5), q = d-2
            except ValueError:
                return None
    return None


def _finish(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]           # K_{d,d}: always valid

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    if start is not None:
        cands.append(start)
    elif d >= 3 and D == 3:
        try:
            base = _pg_base(d)
            if base is not None:
                cands.append(base)
        except Exception:
            pass

    best = _finish(cands, d, D)

    if start is not None and start[0] >= lib.moore_bound(d, D):
        return best

    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 3.0
    if budget > 1.0:
        stdin_graph = best if best[0] > 2 * d else None
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=stdin_graph, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass                                    # keep the valid Python fallback
    return best

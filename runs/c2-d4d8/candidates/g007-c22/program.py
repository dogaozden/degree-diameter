"""Adaptive random-regular annealing variant (experimental, untested).

Different core from the bi-Cayley parent: start from a random d-regular bipartite graph of a
target order N (a circulant Haar graph, mixed by random 2-switches), then anneal the whole
graph with degree-preserving 2-switches against the exact count of pairs at distance > D.
On success the graph grows by two vertices per side (one new edge x-y, then d-1 rewired edges),
and annealing repairs each step. On failure the target order shrinks by about 2%. The best
valid graph is kept throughout, and Python keeps the algebraic start unless C returns a larger
graph that passes lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Snap;

static int d, D;
static long MOORE;
static double t_end;

static int n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static unsigned char side[MAXN];
static int lst[2][MAXN];
static int cnt[2];

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static Snap snap_state, best_state;

static int eu[MAXN * MAXD / 2], ev[MAXN * MAXD / 2];
static int sw[4];
static int stampv[MAXN];
static int stampc = 0;

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

static int hasedge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void repl(int u, int old, int nw) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == old) { adj[u][i] = nw; return; }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void rebuild_lists(void) {
    cnt[0] = cnt[1] = 0;
    for (int v = 0; v < n; v++) lst[side[v]][cnt[side[v]]++] = v;
}

/* Haar graph of Z_h with shifts 0..d-1, h = N/2 (K_{d,d} when N = 2d). */
static void build_circulant(int N) {
    int h = N / 2;
    n = N;
    for (int v = 0; v < n; v++) { deg[v] = 0; side[v] = v >= h ? 1 : 0; }
    for (int a = 0; a < h; a++)
        for (int s = 0; s < d; s++) add_edge(a, h + (a + s) % h);
    rebuild_lists();
}

static int read_start(void) {
    int nn = 0, m = 0;
    if (scanf("%d %d", &nn, &m) != 2) return 0;
    if (nn <= 0 || nn > MAXN || m < 0 || m > MAXN * MAXD / 2) return 0;
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 0;
    n = nn;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= MAXD || deg[v] >= MAXD) return 0;
        if (hasedge(u, v)) return 0;
        add_edge(u, v);
    }
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = 255;
    for (int s = 0; s < n; s++) {
        if (side[s] != 255) continue;
        int h = 0, t = 0;
        side[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (side[u] == 255) { side[u] = 1 - side[v]; q[t++] = u; }
                else if (side[u] == side[v]) return 0;
            }
        }
    }
    for (int v = 0; v < n; v++)
        if (deg[v] != d || side[v] > 1) return 0;
    rebuild_lists();
    return 1;
}

/* Number of unordered pairs at distance > D (bitset ball expansion). */
static long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)adj[v][i] * W;
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
        total += n - c;
    }
    return total / 2;
}

/* Degree-preserving 2-switch on two random A-side edges; applies it if simple. */
static int propose_switch(void) {
    int a1 = lst[0][rndint(cnt[0])];
    int a2 = lst[0][rndint(cnt[0])];
    if (a1 == a2) return 0;
    int b1 = adj[a1][rndint(deg[a1])];
    int b2 = adj[a2][rndint(deg[a2])];
    if (b1 == b2) return 0;
    if (hasedge(a1, b2) || hasedge(a2, b1)) return 0;
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    sw[0] = a1; sw[1] = a2; sw[2] = b1; sw[3] = b2;
    return 1;
}

static void undo_switch(void) {
    int a1 = sw[0], a2 = sw[1], b1 = sw[2], b2 = sw[3];
    repl(a1, b2, b1);
    repl(b2, a1, a2);
    repl(a2, b1, b2);
    repl(b1, a2, a1);
}

static void mix(int rounds) {
    for (int k = 0; k < rounds; k++) propose_switch();
}

/* Metropolis annealing over 2-switches on the pair-distance count. */
static long anneal(long bad, double until, long maxit) {
    double T = 0.6;
    for (long it = 0; it < maxit && bad > 0; it++) {
        if ((it & 7) == 0 && now() >= until) break;
        if (!propose_switch()) continue;
        long nb = bad_pairs();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else undo_switch();
        T *= 0.999;
        if (T < 0.05) T = 0.6;
    }
    return bad;
}

/* Add one vertex per side, joined to each other, with d-1 rewired edges. */
static int grow_two(void) {
    if (n + 2 > MAXN || n + 2 > MOORE) return 0;
    int x = n, y = n + 1;
    n += 2;
    deg[x] = 0;
    deg[y] = 0;
    side[x] = 0;
    side[y] = 1;
    int oldA = cnt[0];
    add_edge(x, y);
    stampc++;
    int k = 0;
    for (long tries = 0; k < d - 1 && tries < 1000000; tries++) {
        int a = lst[0][rndint(oldA)];
        if (stampv[a] == stampc || deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        if (stampv[b] == stampc) continue;
        repl(a, b, y);
        repl(b, a, x);
        adj[x][deg[x]++] = b;
        adj[y][deg[y]++] = a;
        stampv[a] = stampc;
        stampv[b] = stampc;
        k++;
    }
    if (k < d - 1) return 0;
    lst[0][cnt[0]++] = x;
    lst[1][cnt[1]++] = y;
    return 1;
}

static void take(Snap *s) {
    s->n = n;
    for (int v = 0; v < n; v++) {
        s->deg[v] = deg[v];
        s->side[v] = side[v];
        memcpy(s->adj[v], adj[v], sizeof(int) * deg[v]);
    }
}

static void put(const Snap *s) {
    n = s->n;
    for (int v = 0; v < n; v++) {
        deg[v] = s->deg[v];
        side[v] = s->side[v];
        memcpy(adj[v], s->adj[v], sizeof(int) * deg[v]);
    }
    rebuild_lists();
}

static void print_snap(const Snap *s) {
    long m = 0;
    for (int u = 0; u < s->n; u++)
        if (s->side[u] == 0) m += s->deg[u];
    printf("%d %ld\n", s->n, m);
    for (int u = 0; u < s->n; u++)
        if (s->side[u] == 0)
            for (int i = 0; i < s->deg[u]; i++)
                printf("%d %d\n", u, s->adj[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit N0 < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long N0 = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > 31 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    MOORE = moore_bound();

    int have = 0;
    if (read_start() && bad_pairs() == 0) {
        take(&best_state);
        have = 1;
    }
    if (!have) {
        build_circulant(2 * d);
        take(&best_state);
        have = 1;
    }

    /* Fresh random regular graphs at a target order; shrink the target on failure. */
    long N = N0;
    if (N > MOORE) N = MOORE;
    if (N > MAXN) N = MAXN;
    N &= ~1L;
    int ok = 0;
    while (!ok && now() < t_end && N >= 2L * d) {
        double left = t_end - now();
        double until = now() + (left > 6.0 ? 0.5 * left : left);
        build_circulant((int)N);
        mix(20 * n);
        long bad = anneal(bad_pairs(), until, 1L << 60);
        if (bad == 0) {
            ok = 1;
            take(&best_state);
            break;
        }
        long step = 2 * (N / 100 + 1);
        N -= step;
    }

    /* Grow the valid graph by two vertices per side while annealing repairs it. */
    if (ok) {
        int fails = 0;
        while (fails < 4 && now() < t_end && n + 2 <= MOORE && n + 2 <= MAXN) {
            take(&snap_state);
            if (!grow_two()) {
                put(&snap_state);
                break;
            }
            long bad = anneal(bad_pairs(), t_end, 4000);
            if (bad == 0) {
                take(&best_state);
                fails = 0;
            } else {
                put(&snap_state);
                fails++;
            }
        }
    }

    print_snap(&best_state);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def _start_order(d, D):
    """Initial target order for the random-regular search (shrinks on failure in C)."""
    m = lib.moore_bound(d, D)
    n0 = int(0.33 * m)
    n0 -= n0 % 2
    return max(2 * d, n0)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, _start_order(d, D)],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

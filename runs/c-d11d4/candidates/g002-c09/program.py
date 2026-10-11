import itertools
import time

import lib


# C engine: cover-based vertex insertion (bitset balls + randomized greedy set cover),
# degree-stealing insertion (NEW: a cover may take a saturated vertex if one of its edges
# is dropped; the move is kept only if the full diameter check passes), and edge-removal
# kicks that free degree when the diameter check allows it.
C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXDEG 64

typedef uint64_t u64;

static int D_MAX, DIAM, N, W;
static int DEG[MAXN], COL[MAXN];
static int ADJ[MAXN][MAXDEG];
static u64 BALL[MAXN][MAXW], TMP[MAXN][MAXW], RB[MAXN][MAXW];
static u64 FULL[MAXW];
static u64 rs = 1;
static double T0, BUDGET;
static int SN, SDEG[MAXN], SCOL[MAXN], SADJ[MAXN][MAXDEG];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (u64)n); }

static void refresh(void) {
    W = (N + 63) >> 6;
    memset(FULL, 0, sizeof FULL);
    for (int i = 0; i < N; i++) FULL[i >> 6] |= (u64)1 << (i & 63);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < DEG[a]; k++)
        if (ADJ[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    ADJ[a][DEG[a]++] = b;
    ADJ[b][DEG[b]++] = a;
}

static void del_adj(int a, int b) {
    for (int k = 0; k < DEG[a]; k++)
        if (ADJ[a][k] == b) {
            ADJ[a][k] = ADJ[a][--DEG[a]];
            return;
        }
}

static void remove_edge(int a, int b) {
    del_adj(a, b);
    del_adj(b, a);
}

/* out[v] = set of vertices within distance r of v (bitsets over N vertices). */
static void compute_balls(int r, u64 out[][MAXW]) {
    for (int v = 0; v < N; v++) {
        memset(out[v], 0, sizeof(u64) * W);
        out[v][v >> 6] |= (u64)1 << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = TMP[v];
            memcpy(dst, out[v], sizeof(u64) * W);
            for (int k = 0; k < DEG[v]; k++) {
                const u64 *src = out[ADJ[v][k]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++) memcpy(out[v], TMP[v], sizeof(u64) * W);
    }
}

/* True iff every pair of vertices is within distance DIAM. */
static int diameter_ok(void) {
    compute_balls(DIAM, RB);
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++)
            if (RB[v][w] != FULL[w]) return 0;
    return 1;
}

static int color_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < N; v++) COL[v] = -1;
    for (int s = 0; s < N; s++) {
        if (COL[s] >= 0) continue;
        COL[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < DEG[u]; k++) {
                int x = ADJ[u][k];
                if (COL[x] < 0) {
                    COL[x] = 1 - COL[u];
                    q[t++] = x;
                } else if (COL[x] == COL[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 256) return 0;
    N = n;
    for (int v = 0; v < N; v++) DEG[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(u, v)) continue;
        if (DEG[u] >= D_MAX || DEG[v] >= D_MAX) return 0;
        add_edge(u, v);
    }
    return 1;
}

static void set_complete_bip(int d) {
    N = 2 * d;
    for (int v = 0; v < N; v++) DEG[v] = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(i, d + j);
    for (int v = 0; v < N; v++) COL[v] = (v < d) ? 0 : 1;
    refresh();
}

static void save_start(void) {
    SN = N;
    memcpy(SDEG, DEG, sizeof DEG);
    memcpy(SADJ, ADJ, sizeof ADJ);
    memcpy(SCOL, COL, sizeof COL);
}

static void restore_start(void) {
    N = SN;
    memcpy(DEG, SDEG, sizeof DEG);
    memcpy(ADJ, SADJ, sizeof ADJ);
    memcpy(COL, SCOL, sizeof COL);
    refresh();
}

/* Randomized greedy cover of FULL by at most D_MAX balls (BALL must be current).
   Candidates have colour != nc; saturated ones are used only if allow_full.
   Writes the chosen vertices into S and returns their count, or -1. */
static int find_cover(int nc, int *S, int randomize, int allow_full) {
    static int cand[MAXN], gain[MAXN];
    int nca = 0;
    for (int s = 0; s < N; s++)
        if (COL[s] != nc && (allow_full || DEG[s] < D_MAX)) cand[nca++] = s;
    u64 cov[MAXW];
    memset(cov, 0, sizeof(u64) * W);
    int ns = 0;
    for (;;) {
        int full = 1;
        for (int w = 0; w < W; w++)
            if (cov[w] != FULL[w]) { full = 0; break; }
        if (full) return ns;
        if (ns >= D_MAX || nca == 0) return -1;
        int best = 0;
        for (int i = 0; i < nca; i++) {
            const u64 *b = BALL[cand[i]];
            int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(b[w] & ~cov[w]);
            gain[i] = g;
            if (g > best) best = g;
        }
        if (best == 0) return -1;
        int thr = best;
        if (randomize && best > 1 && rndint(10) < 3) thr = best - 1;
        int pick = -1, cnt = 0;
        for (int i = 0; i < nca; i++) {
            if (gain[i] < thr || gain[i] <= 0) continue;
            if (!randomize) { pick = i; break; }
            cnt++;
            if (rndint(cnt) == 0) pick = i;
        }
        if (pick < 0) return -1;
        S[ns++] = cand[pick];
        const u64 *b = BALL[cand[pick]];
        for (int w = 0; w < W; w++) cov[w] |= b[w];
        cand[pick] = cand[--nca];
    }
}

/* Insert a new vertex whose neighbourhood is a cover; keeps diameter by construction. */
static int try_grow(int attempts) {
    if (N + 1 >= MAXN) return 0;
    compute_balls(DIAM - 1, BALL);
    int first = rndint(2);
    for (int side = 0; side < 2; side++) {
        int nc = side == 0 ? first : 1 - first;
        for (int a = 0; a < attempts; a++) {
            int S[MAXDEG];
            int ns = find_cover(nc, S, a > 0, 0);
            if (ns > 0) {
                int v = N;
                N++;
                COL[v] = nc;
                DEG[v] = 0;
                for (int i = 0; i < ns; i++) add_edge(v, S[i]);
                refresh();
                return 1;
            }
        }
    }
    return 0;
}

/* Degree-stealing insertion: saturated cover vertices give up one random edge.
   Kept only if the full diameter check passes; otherwise everything is undone. */
static int try_steal(void) {
    if (N + 1 >= MAXN) return 0;
    compute_balls(DIAM - 1, BALL);
    int nc = rndint(2);
    int S[MAXDEG];
    int ns = find_cover(nc, S, 1, 1);
    if (ns <= 0) return 0;
    int nsat = 0;
    for (int i = 0; i < ns; i++)
        if (DEG[S[i]] >= D_MAX) nsat++;
    if (nsat > 3) return 0;
    int ra[MAXDEG], rb[MAXDEG], nr = 0;
    for (int i = 0; i < ns; i++) {
        int s = S[i];
        if (DEG[s] >= D_MAX) {
            int t = ADJ[s][rndint(DEG[s])];
            remove_edge(s, t);
            ra[nr] = s;
            rb[nr] = t;
            nr++;
        }
    }
    int v = N;
    N++;
    COL[v] = nc;
    DEG[v] = 0;
    for (int i = 0; i < ns; i++) add_edge(v, S[i]);
    refresh();
    if (diameter_ok()) return 1;
    for (int i = 0; i < ns; i++) remove_edge(S[i], v);
    DEG[v] = 0;
    N--;
    refresh();
    for (int r = 0; r < nr; r++) add_edge(ra[r], rb[r]);
    return 0;
}

/* Kick: drop a random edge if the graph stays valid; frees degree for later moves. */
static void kick_one(void) {
    for (int tries = 0; tries < 6; tries++) {
        int a = rndint(N);
        if (DEG[a] == 0) continue;
        int b = ADJ[a][rndint(DEG[a])];
        remove_edge(a, b);
        if (diameter_ok()) return;
        add_edge(a, b);
    }
}

static void print_graph(void) {
    long m = 0;
    for (int v = 0; v < N; v++) m += DEG[v];
    m /= 2;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < DEG[v]; k++)
            if (ADJ[v][k] > v) printf("%d %d\n", v, ADJ[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    D_MAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)atoll(argv[3]) * 0xBF58476D1CE4E5B9ULL);
    if (rs == 0) rs = 1;
    BUDGET = atof(argv[4]);
    if (D_MAX < 1 || D_MAX > MAXDEG || DIAM < 1) { printf("1 0\n"); return 0; }
    if (DIAM < 2) { printf("2 1\n0 1\n"); return 0; }
    T0 = now();

    int ok = 0;
    N = 0;
    if (read_input()) {
        refresh();
        ok = color_graph() && diameter_ok();
    }
    if (!ok) set_complete_bip(D_MAX);
    save_start();

    while (now() - T0 < BUDGET) {
        if (try_grow(8)) continue;
        int done = 0;
        for (int t = 0; t < 4 && !done; t++) done = try_steal();
        if (done) continue;
        kick_one();
    }

    refresh();
    if (!color_graph() || !diameter_ok()) restore_start();
    print_graph();
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    if D >= 2 and d >= 2:
        start = None
        if D >= 4:
            start = _best_gq(d)
        if start is None and D >= 3:
            start = _best_pg(d)
        if start is None:
            start = best
        consider(start)
        if time.monotonic() - t_start < time_limit * 0.5:
            budget = max(0.5, 0.8 * time_limit - 2.0)
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, int(seed) & 0x7FFFFFFF, f"{budget:.2f}"],
                    stdin_graph=start,
                    timeout=max(1.0, 0.92 * time_limit),
                )
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

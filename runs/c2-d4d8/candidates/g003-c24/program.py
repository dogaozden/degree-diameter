"""Bi-Cayley search over projective linear groups (replaces the metacyclic lift search).

Construction: a bipartite graph on two copies of a finite group G, with A_g adjacent to B_{g s}
for s in a d-element set S of G. Left multiplication is an automorphism that is regular on each
side, so the diameter is at most D iff BFS from A_e and from B_e reaches everything within D.
The groups are PSL(2,p) and PGL(2,p) for small primes p, built inside C from 2x2 matrices mod p.
The search anneals S against the count of unreached vertices, and successes are re-checked with
the full bitset validator. The start graph from Python is kept unless a valid, larger graph is found.
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
#define GCAP 2600
#define MAXV (2 * GCAP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long MOORE;
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

/* Number of unordered pairs at distance > D (bitset ball expansion). */
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

/* ---------------- finite group PSL(2,p) / PGL(2,p) as permutation-free table ---------------- */

static int Q;                       /* current prime */
static int GN;                      /* current group order */
static int GID;                     /* index of identity */
static int ECODE[GCAP];             /* normalized matrix code of each element */
static int IDX[83521];              /* code -> element index, or -1 */
static int INVT[32];                /* modular inverses mod Q */
static uint16_t MT[GCAP * GCAP];    /* MT[i*GN+j] = index of i*j */
static int INV[GCAP];               /* group inverse */

static int modq(int x) {
    x %= Q;
    if (x < 0) x += Q;
    return x;
}

static int inv_mod(int x) {
    long r = 1, b = x, e = Q - 2;
    b %= Q;
    while (e > 0) {
        if (e & 1) r = r * b % Q;
        b = b * b % Q;
        e >>= 1;
    }
    return (int)r;
}

/* Encode a matrix after scaling so its first nonzero entry is 1. Returns -1 for the zero matrix. */
static int enc_norm(int a, int b, int c, int e) {
    int v[4] = {a, b, c, e};
    int f = 0;
    for (int i = 0; i < 4; i++)
        if (v[i]) { f = v[i]; break; }
    if (!f) return -1;
    int fi = INVT[f];
    for (int i = 0; i < 4; i++) v[i] = v[i] * fi % Q;
    return ((v[0] * Q + v[1]) * Q + v[2]) * Q + v[3];
}

static int is_square_mod(int x) {
    for (int y = 1; y < Q; y++)
        if (y * y % Q == x) return 1;
    return 0;
}

/* type 0 = PSL(2,q) (determinant a square), type 1 = PGL(2,q). Returns 1 on success. */
static int build_group(int type, int q) {
    Q = q;
    for (int x = 1; x < Q; x++) INVT[x] = inv_mod(x);
    int nC = Q * Q * Q * Q;
    for (int c = 0; c < nC; c++) IDX[c] = -1;
    int cnt = 0;
    for (int code = 0; code < nC; code++) {
        int a = code / (Q * Q * Q);
        int b = (code / (Q * Q)) % Q;
        int c = (code / Q) % Q;
        int e = code % Q;
        int det = modq(a * e - b * c);
        if (det == 0) continue;
        int v[4] = {a, b, c, e};
        int f = 0;
        for (int i = 0; i < 4; i++)
            if (v[i]) { f = v[i]; break; }
        if (f != 1) continue;
        if (type == 0 && !is_square_mod(det)) continue;
        if (cnt >= GCAP) return 0;
        ECODE[cnt] = code;
        IDX[code] = cnt;
        cnt++;
    }
    GN = cnt;
    int idc = ((1 * Q + 0) * Q + 0) * Q + 1;
    if (IDX[idc] < 0) return 0;
    GID = IDX[idc];
    for (int i = 0; i < GN; i++) {
        int ci = ECODE[i];
        int A0 = ci / (Q * Q * Q), A1 = (ci / (Q * Q)) % Q, A2 = (ci / Q) % Q, A3 = ci % Q;
        for (int j = 0; j < GN; j++) {
            int cj = ECODE[j];
            int B0 = cj / (Q * Q * Q), B1 = (cj / (Q * Q)) % Q, B2 = (cj / Q) % Q, B3 = cj % Q;
            int p0 = (A0 * B0 + A1 * B2) % Q;
            int p1 = (A0 * B1 + A1 * B3) % Q;
            int p2 = (A2 * B0 + A3 * B2) % Q;
            int p3 = (A2 * B1 + A3 * B3) % Q;
            int c2 = enc_norm(p0, p1, p2, p3);
            if (c2 < 0 || IDX[c2] < 0) return 0;
            MT[(size_t)i * GN + j] = (uint16_t)IDX[c2];
        }
    }
    for (int i = 0; i < GN; i++) INV[i] = -1;
    for (int i = 0; i < GN; i++)
        for (int j = 0; j < GN; j++)
            if (MT[(size_t)i * GN + j] == GID) { INV[i] = j; break; }
    for (int i = 0; i < GN; i++)
        if (INV[i] < 0) return 0;
    return 1;
}

/* Candidate groups, largest vertex count first. */
typedef struct { int type, q, N; } Cand;
static Cand cands[16];
static int ncand = 0;

static void make_cands(void) {
    static const int primes[] = {3, 5, 7, 11, 13, 17};
    ncand = 0;
    for (int i = 0; i < 6; i++) {
        long p = primes[i];
        long pg = p * (p * p - 1);
        if (pg <= GCAP) {
            cands[ncand].type = 1; cands[ncand].q = (int)p; cands[ncand].N = (int)pg; ncand++;
        }
        if (pg / 2 <= GCAP) {
            cands[ncand].type = 0; cands[ncand].q = (int)p; cands[ncand].N = (int)(pg / 2); ncand++;
        }
    }
    for (int i = 0; i < ncand; i++)
        for (int j = i + 1; j < ncand; j++)
            if (cands[j].N > cands[i].N) {
                Cand t = cands[i]; cands[i] = cands[j]; cands[j] = t;
            }
}

/* ---------------- bi-Cayley diameter test and annealing ---------------- */

static int vis[MAXV];
static int stampc = 0;
static int queue_[MAXV];

/* BFS up to depth D_ from src; returns the number of vertices reached. */
static int bfs_count(int src, const int *S, const int *Si) {
    int N = GN;
    stampc++;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    vis[src] = stampc;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = queue_[head++];
            if (v < N) {
                const uint16_t *row = MT + (size_t)v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[S[i]];
                    if (vis[u] != stampc) { vis[u] = stampc; queue_[tail++] = u; }
                }
            } else {
                int h = v - N;
                const uint16_t *row = MT + (size_t)h * N;
                for (int i = 0; i < d; i++) {
                    int u = row[Si[i]];
                    if (vis[u] != stampc) { vis[u] = stampc; queue_[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of vertices not within distance D of A_e or B_e (0 iff diameter <= D). */
static long eval_S(const int *S) {
    static int Si[MAXD];
    for (int i = 0; i < d; i++) Si[i] = INV[S[i]];
    int ra = bfs_count(GID, S, Si);
    int rb = bfs_count(GN + GID, S, Si);
    return (long)(2 * GN - ra) + (long)(2 * GN - rb);
}

static int in_set(int x, const int *S, int k) {
    for (int i = 0; i < k; i++)
        if (S[i] == x) return 1;
    return 0;
}

static void build_graph(Graph *g, const int *S) {
    int N = GN;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            int u = N + MT[(size_t)x * N + S[i]];
            add_edge(g, x, u);
        }
}

static Graph best;

/* Anneal a d-subset S of the current group until the bi-Cayley graph has diameter <= D. */
static int search_group(double until) {
    int N = GN;
    static int S[MAXD];
    static Graph cand;
    if (N < d) return 0;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_set(x, S, i));
            S[i] = x;
        }
        long bad = eval_S(S);
        double temp = 2.0;
        for (int it = 0; it < 6000 && bad > 0; it++) {
            if ((it & 31) == 0 && now() > until) break;
            int i = rndint(d);
            int x = rndint(N);
            if (in_set(x, S, d)) continue;
            int old = S[i];
            S[i] = x;
            long nb = eval_S(S);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / temp)) bad = nb;
            else S[i] = old;
            temp *= 0.999;
            if (temp < 0.2) temp = 2.0;
        }
        if (bad == 0) {
            build_graph(&cand, S);
            if (cand.n > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                return 1;
            }
        }
    }
    return 0;
}

/* Visit groups largest first; each visit gets a share of the remaining time. */
static void run_groups(double until) {
    make_cands();
    int cur_type = -1, cur_q = -1;
    while (now() < until) {
        int any = 0;
        for (int c = 0; c < ncand; c++) {
            long sz = 2L * cands[c].N;
            if (sz <= best.n || sz > MOORE || cands[c].N < d) continue;
            double left = until - now();
            if (left <= 0.05) return;
            if (cur_type != cands[c].type || cur_q != cands[c].q) {
                cur_type = -1;
                cur_q = -1;
                if (!build_group(cands[c].type, cands[c].q)) continue;
                cur_type = cands[c].type;
                cur_q = cands[c].q;
            }
            any = 1;
            double slice = left * 0.3;
            if (slice > left) slice = left;
            search_group(now() + slice);
        }
        if (!any) return;
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

    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < MOORE) run_groups(t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

"""Two-stage search for the bipartite degree-diameter problem.

Stage 1 is the parent's affine-group Haar lift search (C_HAAR). It gives the
valid fallback and normally sets the incumbent order.

Stage 2 is the new, different construction (C_ANNEAL). It ignores group
structure. It starts from a circulant bipartite d-regular graph on N + N
vertices, mixes it with random degree-preserving 2-switches, and anneals the
number of vertex pairs at distance more than D. Each switch keeps the graph
simple and d-regular. Cost is computed exactly with bitset ball expansion.
Target N is one more than the incumbent's half-order, so success means a
strictly larger valid graph. Any failure keeps the incumbent.
"""
import itertools
import time

import lib

C_HAAR = r'''
/* Affine-group Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 8192
#define MAXD 32
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

/* Multiply field elements a, b (base-p digit vectors) modulo the monic f with digits m. */
static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;   /* zero divisor: reducible */
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). Product:
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, Sinv[i]);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity on each side means two BFS runs (from L_e and R_e) decide diameter. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Iterated annealing over the connection set S of size d in the current group.
 * The first round starts from a random set. Later rounds start from the incumbent
 * (the lowest-cost set seen so far) with two elements replaced, at a lower starting
 * temperature, so time concentrates near good sets.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    int incS[MAXD];
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incS, S, sizeof(int) * (size_t)d);
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    /* Ascending order from lo: the smallest orders above the current best are the
     * ones that can beat the record, so each attempt gets 20% of the remaining time
     * (at least 1 s). Failed attempts shrink the pool only slowly. */
    int best_idx = -1, bestN = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].N <= bestN) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        if (search_group(now() + slice)) {
            bestN = GN;
            best_idx = ci;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
    print_result();
    return 0;
}
'''

C_ANNEAL = r'''
/* Random-regular bipartite annealing for a fixed half-order N.
 * Usage: prog d D seed time_limit N     (stdin ignored)
 * Start: circulant d-regular bipartite graph on N+N vertices, mixed by random
 * degree-preserving 2-switches. Then anneal the count of ordered pairs at
 * distance > D (exact, via bitset ball expansion) using 2-switches.
 * Output: "2N dN" and edges on success, else "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXV (2 * MAXN)
#define MAXW (MAXV / 64)
#define MAXD 24

static int d, D, N, V, W;
static int adj[MAXV][MAXD];
static uint64_t RA[MAXV][MAXW], RB[MAXV][MAXW];
static uint64_t rs = 0x2545F4914F6CDD1DULL;
static double t_end;

typedef struct { int a1, k1, b1, kb1, a2, k2, b2, kb2; } Mv;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < d; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static int pos_of(int v, int u) {
    for (int k = 0; k < d; k++)
        if (adj[v][k] == u) return k;
    return -1;
}

/* Number of ordered pairs (x, y) with dist(x, y) > D. */
static long cost(void) {
    W = (V + 63) / 64;
    for (int v = 0; v < V; v++) {
        for (int w = 0; w < W; w++) RA[v][w] = 0;
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA, (*nxt)[MAXW] = RB;
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < V; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < d; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < V; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += V - c;
    }
    return bad;
}

static void init_circulant(void) {
    int sh[MAXD], ns = 0;
    while (ns < d) {
        int s = rndint(N), ok = 1;
        for (int i = 0; i < ns; i++)
            if (sh[i] == s) ok = 0;
        if (ok) sh[ns++] = s;
    }
    int cnt[MAXV];
    for (int b = 0; b < V; b++) cnt[b] = 0;
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d; k++) {
            int b = N + (a + sh[k]) % N;
            adj[a][k] = b;
            adj[b][cnt[b]++] = a;
        }
}

/* Propose a 2-switch on random left vertices. Returns 0 if the switch is invalid. */
static int propose(Mv *m) {
    m->a1 = rndint(N);
    m->k1 = rndint(d);
    m->b1 = adj[m->a1][m->k1];
    m->a2 = rndint(N);
    m->k2 = rndint(d);
    m->b2 = adj[m->a2][m->k2];
    if (m->a1 == m->a2 || m->b1 == m->b2) return 0;
    if (has_edge(m->a1, m->b2) || has_edge(m->a2, m->b1)) return 0;
    m->kb1 = pos_of(m->b1, m->a1);
    m->kb2 = pos_of(m->b2, m->a2);
    return 1;
}

/* (a1,b1),(a2,b2) become (a1,b2),(a2,b1). */
static void do_mv(const Mv *m) {
    adj[m->a1][m->k1] = m->b2;
    adj[m->b2][m->kb2] = m->a1;
    adj[m->a2][m->k2] = m->b1;
    adj[m->b1][m->kb1] = m->a2;
}

static void undo_mv(const Mv *m) {
    adj[m->a1][m->k1] = m->b1;
    adj[m->b1][m->kb1] = m->a1;
    adj[m->a2][m->k2] = m->b2;
    adj[m->b2][m->kb2] = m->a2;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    N = atoi(argv[5]);
    if (d < 2 || d > MAXD || D < 2 || N < d || N > MAXN) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    V = 2 * N;
    init_circulant();
    Mv m;
    long mix = 4L * N * d;
    for (long t = 0; t < mix; t++)
        if (propose(&m)) do_mv(&m);

    long cur = cost();
    double Ts = 1.0 + 0.05 * (double)cur, Te = 0.3, T = Ts;
    double ts = now(), span = t_end - ts;
    if (span < 0.1) span = 0.1;
    long it = 0;
    while (cur > 0) {
        if ((it & 3) == 0) {
            double tn = now();
            if (tn >= t_end) break;
            double f = (tn - ts) / span;
            T = Ts * pow(Te / Ts, f);
        }
        it++;
        if (!propose(&m)) continue;
        do_mv(&m);
        long c2 = cost();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            undo_mv(&m);
        }
    }
    if (cur > 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", V, N * d);
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", a, adj[a][k]);
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def elapsed():
        return time.monotonic() - t0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Stage 1: parent's Haar-lift search over F_q x| H. This is the valid incumbent.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.7 * time_limit - elapsed() - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 3
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_HAAR, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

    # Stage 2: anneal a random-regular bipartite graph just above the incumbent.
    # Each success raises the target by one half-order step.
    if d >= 2 and D >= 2:
        N = best[0] // 2 + 1
        for _ in range(6):
            remaining = 0.85 * time_limit - elapsed() - 2.0
            if remaining < 4.0 or N > 2048 or N < d:
                break
            try:
                text = lib.run_c(C_ANNEAL, [d, D, seed + N, round(remaining, 2), N],
                                 stdin_graph=None, timeout=remaining + 8.0)
                n, e = lib.parse_graph_text(text)
            except Exception:
                break
            if n == 0:
                break
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                N = n // 2 + 1
            else:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

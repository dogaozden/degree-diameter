"""Bi-Cayley search over non-metacyclic groups (PSL/PGL/SL(2,p) x Z_k, plus metacyclic).

A bi-Cayley graph on two copies of a group G (order N) with connection set S, |S| = d, is d-regular,
bipartite, and has 2N vertices. Left multiplication is an automorphism acting regularly on each side,
so the diameter test reduces to two BFS runs, one from each side's identity. The C engine picks a
group (from a precomputed list of matrix-group products, or a random metacyclic group), then
hill-climbs S inside that group, growing the order past the best graph found so far.

Python builds the algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez, K_{d,d}), checks them with
lib.is_valid, and only accepts the C output if it is valid and strictly larger.
"""
import time

import itertools

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
#define MAXG 2700
#define BMAX 2200
#define MAXC 512

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int type, q, k, N; } Cand;

static int d, D;
static long MOORE;
static int NMAX;
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

/* ---------------- groups ---------------- */

/* MT[x*N+y] = x*y for the current group of order GN; GINV[x] = inverse of x. Identity is index 0. */
static uint16_t MT[MAXG * MAXG];
static uint16_t BT[BMAX * BMAX];
static int GN;
static int GINV[MAXG];
static int RP[MAXG];
static int BM = 0;
static int base_key = -1;
static int elem_code[BMAX];
static int CI[28561];
static int EA[BMAX], EB[BMAX], EC[BMAX], EE[BMAX];

static int md(int x, int q) { x %= q; if (x < 0) x += q; return x; }

static int ipow(int b, int e, int q) {
    long r = 1, bb = md(b, q);
    while (e > 0) {
        if (e & 1) r = r * bb % q;
        bb = bb * bb % q;
        e >>= 1;
    }
    return (int)r;
}

static int minv(int x, int q) { return ipow(x, q - 2, q); }

/* Canonical code of the matrix (a b; c e) in PGL (type 0), PSL (type 1) or SL (type 2) over GF(q),
 * or -1 if it is not in the group. */
static int canon_code(int a, int b, int c, int e, int q, int type) {
    a = md(a, q); b = md(b, q); c = md(c, q); e = md(e, q);
    if (type != 2) {
        int f = a ? a : (b ? b : (c ? c : e));
        if (!f) return -1;
        int iv = minv(f, q);
        a = a * iv % q; b = b * iv % q; c = c * iv % q; e = e * iv % q;
    }
    int det = md(a * e - b * c, q);
    if (det == 0) return -1;
    if (type == 2) { if (det != 1) return -1; }
    else if (type == 1) { if (ipow(det, (q - 1) / 2, q) != 1) return -1; }
    return ((a * q + b) * q + c) * q + e;
}

static void build_inv(void) {
    int N = GN;
    for (int i = 0; i < N; i++) {
        GINV[i] = 0;
        const uint16_t *row = MT + (size_t)i * N;
        for (int j = 0; j < N; j++)
            if (row[j] == 0) { GINV[i] = j; break; }
    }
}

/* Multiplication table of PGL/PSL/SL(2,q), q prime, stored in BT (order BM). */
static void build_base(int q, int type) {
    int key = q * 4 + type;
    if (key == base_key) return;
    base_key = key;
    int Q4 = q * q * q * q;
    for (int i = 0; i < Q4; i++) CI[i] = -1;
    int id = canon_code(1, 0, 0, 1, q, type);
    int M = 0;
    elem_code[M] = id; CI[id] = M; M++;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    int code = ((a * q + b) * q + c) * q + e;
                    if (code == id || M >= BMAX) continue;
                    if (canon_code(a, b, c, e, q, type) != code) continue;
                    elem_code[M] = code;
                    CI[code] = M;
                    M++;
                }
    BM = M;
    for (int x = 0; x < M; x++) {
        int code = elem_code[x];
        EE[x] = code % q; code /= q;
        EC[x] = code % q; code /= q;
        EB[x] = code % q; code /= q;
        EA[x] = code % q;
    }
    for (int x = 0; x < M; x++)
        for (int y = 0; y < M; y++) {
            int a = (EA[x] * EA[y] + EB[x] * EC[y]) % q;
            int b = (EA[x] * EB[y] + EB[x] * EE[y]) % q;
            int c = (EC[x] * EA[y] + EE[x] * EC[y]) % q;
            int e = (EC[x] * EB[y] + EE[x] * EE[y]) % q;
            int cv = canon_code(a, b, c, e, q, type);
            int idx = (cv >= 0) ? CI[cv] : 0;
            if (idx < 0) idx = 0;
            BT[x * M + y] = (uint16_t)idx;
        }
}

/* Direct product of the base group (order BM) with Z_k. */
static void build_product(int k) {
    int N = BM * k;
    GN = N;
    for (int x = 0; x < BM; x++)
        for (int c = 0; c < k; c++) {
            uint16_t *row = MT + (size_t)(x * k + c) * N;
            for (int y = 0; y < BM; y++) {
                int bxy = (int)BT[x * BM + y] * k;
                for (int f = 0; f < k; f++)
                    row[y * k + f] = (uint16_t)(bxy + (c + f) % k);
            }
        }
    build_inv();
}

/* Metacyclic group Z_m x| Z_k with action r, element a*k+b. */
static void build_meta(int m, int k, int r) {
    int N = m * k;
    GN = N;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        uint16_t *row = MT + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            long v = ((a + (long)RP[b] * c) % m) * k + (b + e) % k;
            row[y] = (uint16_t)v;
        }
    }
    build_inv();
}

static int pick_meta(int N, int *om, int *ok, int *orr) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    *om = bm; *ok = bk; *orr = br;
    return 1;
}

static Cand cands[MAXC];
static int ncand = 0;

static void build_cands(void) {
    static const int qs[4] = {5, 7, 11, 13};
    ncand = 0;
    for (int qi = 0; qi < 4; qi++)
        for (int type = 0; type < 3; type++) {
            long q = qs[qi];
            long BO = q * (q * q - 1);
            if (type == 1) BO /= 2;
            for (long k = 1; BO * k <= NMAX; k++) {
                long N = BO * k;
                if (N < d) continue;
                if (ncand >= MAXC) break;
                cands[ncand].type = type;
                cands[ncand].q = (int)q;
                cands[ncand].k = (int)k;
                cands[ncand].N = (int)N;
                ncand++;
            }
        }
    for (int i = 1; i < ncand; i++) {
        Cand t = cands[i];
        int j = i - 1;
        while (j >= 0 && cands[j].N > t.N) { cands[j + 1] = cands[j]; j--; }
        cands[j + 1] = t;
    }
}

/* ---------------- bi-Cayley search ---------------- */

static int VD[2 * MAXG], VQ[2 * MAXG];
static int SINV[MAXD];

/* Unreached pairs for the bi-Cayley graph A=G, B=G, g ~ g*s (s in S).
 * Zero iff diameter <= D (BFS from A identity covers everything, BFS from B identity covers B). */
static long score_S(const int *S) {
    int N = GN, V = 2 * N;
    for (int j = 0; j < d; j++) SINV[j] = GINV[S[j]];
    long bad = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) VD[v] = -1;
        int head = 0, tail = 0;
        VD[s0] = 0;
        VQ[tail++] = s0;
        while (head < tail) {
            int v = VQ[head++];
            int dv = VD[v];
            if (dv >= D) continue;
            if (v < N) {
                const uint16_t *row = MT + (size_t)v * N;
                for (int j = 0; j < d; j++) {
                    int u = N + (int)row[S[j]];
                    if (VD[u] < 0) { VD[u] = dv + 1; VQ[tail++] = u; }
                }
            } else {
                const uint16_t *row = MT + (size_t)(v - N) * N;
                for (int j = 0; j < d; j++) {
                    int u = (int)row[SINV[j]];
                    if (VD[u] < 0) { VD[u] = dv + 1; VQ[tail++] = u; }
                }
            }
        }
        if (src == 0) {
            bad += V - tail;
        } else {
            int cb = 0;
            for (int i = 0; i < tail; i++) if (VQ[i] >= N) cb++;
            bad += N - cb;
        }
    }
    return bad;
}

static void pick_S_random(int N, int *S) {
    for (int j = 0; j < d; j++) {
        int x, ok;
        do {
            x = rndint(N);
            ok = 1;
            for (int i = 0; i < j; i++) if (S[i] == x) { ok = 0; break; }
        } while (!ok);
        S[j] = x;
    }
}

static int contains_except(const int *S, int j, int x) {
    for (int i = 0; i < d; i++) if (i != j && S[i] == x) return 1;
    return 0;
}

/* Simulated-annealing hill climb over the connection set S inside the current group. */
static int hill(int N, double until, int *outS) {
    int S[MAXD];
    while (now() < until) {
        pick_S_random(N, S);
        long cur = score_S(S);
        double T = 2.0;
        for (int it = 0; it < 20000 && cur > 0; it++) {
            if ((it & 255) == 0 && now() > until) return 0;
            int j = rndint(d), x = rndint(N);
            if (contains_except(S, j, x)) continue;
            int old = S[j];
            S[j] = x;
            long nw = score_S(S);
            if (nw <= cur || rnd01() < exp((double)(cur - nw) / T)) cur = nw;
            else S[j] = old;
            T *= 0.9997;
            if (T < 0.2) T = 2.0;
        }
        if (cur == 0) {
            memcpy(outS, S, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
}

static void build_bicayley(Graph *g, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int j = 0; j < d; j++)
            add_edge(g, x, N + (int)MT[(size_t)x * N + S[j]]);
}

static Graph best, gcand;

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
    t_end = t0 + limit * 0.88;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD - 1) {
        printf("1 0\n");
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long mh = MOORE / 2;
    NMAX = (int)(mh < MAXG ? mh : MAXG);
    build_cands();

    while (now() < t_end) {
        int floorN = best.n / 2;
        if (floorN + 1 > NMAX) break;
        double left = t_end - now();
        double slice = left < 2.5 ? left : 2.5;
        if (slice < 0.05) break;

        int f0 = 0;
        while (f0 < ncand && cands[f0].N <= floorN) f0++;
        int cnt = ncand - f0;

        if (cnt == 0 || rndint(3) == 0) {
            int span = NMAX - floorN;
            if (span > 64) span = 64;
            int NN = floorN + 1 + rndint(span);
            int m, k, r;
            if (!pick_meta(NN, &m, &k, &r)) continue;
            build_meta(m, k, r);
        } else {
            int pick = f0 + rndint(cnt < 4 ? cnt : 4);
            build_base(cands[pick].q, cands[pick].type);
            build_product(cands[pick].k);
        }

        int N = GN;
        if (N < d || N <= floorN || 2 * N > MAXN) continue;
        int S[MAXD];
        if (hill(N, now() + slice, S)) {
            build_bicayley(&gcand, N, S);
            if (gcand.n > best.n && is_valid(&gcand)) copy_graph(&best, &gcand);
        }
    }

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

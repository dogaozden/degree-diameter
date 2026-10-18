"""Program: bi-Cayley search over metacyclic groups Z_m x| Z_k and PSL/SL(2,q),
followed by degree-preserving vertex insertion.

Phase 1 (bi-Cayley): as in the parent. Left multiplication by G acts as
automorphisms, so diameter <= D is checked with two BFS balls. Runs for the first
35% of the usable time, or is skipped when a valid start graph is given on stdin.

Phase 2 (new: insertion plus plateau walk): the graph stays d-regular and bipartite.
  * Insert: pick d pairwise-disjoint edges a_i-b_i (a_i in A, b_i in B). Create new
    vertices An (side A) and Bn (side B). Replace a_i-b_i by a_i-Bn and b_i-An, then
    join An to all b_i and Bn to all a_i. Every old degree is kept, the order grows by
    2, and the result is accepted only if the full diameter test passes; otherwise it
    is reverted.
  * Walk: when insertion fails, apply a random double-edge swap (a1-b1, a2-b2 ->
    a1-b2, a2-b1), kept only if the graph is still valid. This moves the graph around
    the valid plateau so later insertions get fresh chances.
The diameter test is a full bitset ball computation over all vertices, so the output
is always valid.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXDEG 8
#define MAXCAND 48
#define MAXV (2 * MAXN + 2048)
#define WMAX ((MAXV + 63) / 64)

static int d, D;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------------ group */

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

/* PSL(2,q) or SL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    double frac;
} Cand;

static Cand all[3 * MAXCAND + 32];
static Cand hi_c[MAXCAND], lo_c[MAXCAND];
static Cand bestc;
static int bS[MAXDEG];

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_meta(int Nval, Cand *arr, int *cnt) {
    for (int k = 2; k <= Nval / 3 && *cnt < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            c.frac = 0.06;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + s];
        Ri[k][x] = (int)T[(size_t)x * N + si];
    }
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------------ BFS cost (phase 1) */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + Rr[k][v];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 4000) {
            randomize_S();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ graph state */

static int V = 0;
static int adj[MAXV][MAXDEG];
static int deg[MAXV];
static int side[MAXV];
static uint64_t bufA[(size_t)MAXV * WMAX];
static uint64_t bufB[(size_t)MAXV * WMAX];
static int mark[MAXV];
static int markt = 0;

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    long sum = 0;
    for (int v = 0; v < V; v++) sum += deg[v];
    printf("%d %ld\n", V, sum / 2);
    for (int v = 0; v < V; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < adj[v][k]) printf("%d %d\n", v, adj[v][k]);
}

/* Full diameter test by bitset balls. Returns 1 iff every pair is within D. */
static int check_valid(void) {
    if (V < 1) return 0;
    int W = (V + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)V * (size_t)W);
    for (int v = 0; v < V; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < D; lvl++) {
        for (int v = 0; v < V; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *nb = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= nb[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    uint64_t last = (V & 63) ? ((1ULL << (V & 63)) - 1ULL) : ~0ULL;
    for (int v = 0; v < V; v++) {
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W - 1; w++)
            if (row[w] != ~0ULL) return 0;
        if (row[W - 1] != last) return 0;
    }
    return 1;
}

static void repl(int *list, int len, int oldv, int newv) {
    for (int k = 0; k < len; k++)
        if (list[k] == oldv) { list[k] = newv; return; }
}

static int has_nb(const int *list, int len, int v) {
    for (int k = 0; k < len; k++)
        if (list[k] == v) return 1;
    return 0;
}

/* Load a start graph from stdin. Returns 1 if loaded, 0 if "0 0", -1 if unusable. */
static int load_stdin(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0) return 0;
    if (n > MAXV - 2 || m < 0 || m > n * MAXDEG) return -1;
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return -1;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return -1;
        if (deg[u] >= d || deg[v] >= d) return -1;
        if (has_nb(adj[u], deg[u], v)) return -1;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    V = n;
    for (int i = 0; i < n; i++) side[i] = -1;
    static int stk[MAXV];
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int top = 0;
        stk[top++] = s;
        while (top > 0) {
            int x = stk[--top];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    stk[top++] = y;
                } else if (side[y] == side[x]) {
                    return -1;
                }
            }
        }
    }
    return 1;
}

/* Load the bi-Cayley graph found by phase 1: A_x ~ B_{x s_k}. */
static void load_phase1(void) {
    V = 2 * N;
    for (int x = 0; x < N; x++) {
        deg[x] = d;
        side[x] = 0;
        deg[N + x] = d;
        side[N + x] = 1;
        for (int k = 0; k < d; k++) {
            adj[x][k] = N + Rr[k][x];
            adj[N + x][k] = Ri[k][x];
        }
    }
}

/* ------------------------------------------------------------------ phase 1 */

static int phase1(double until, long ref) {
    long moore = moore_bound();
    long bestN = d;
    int have = 0;
    long recHalf = ref / 2;
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = (int)recHalf + 1;
    int na = 0, nh = 0, nl = 0;

    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            if (na >= 16) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            c.frac = 0.25;
            all[na++] = c;
        }
    }
    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, lo_c, &nl);
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv, hi_c, &nh);
    for (int i = 0; i < nl; i++) all[na++] = lo_c[i];
    for (int i = 0; i < nh; i++) all[na++] = hi_c[i];

    double budget0 = until - now();
    double base_slice = budget0 * 0.03;
    if (base_slice < 0.3) base_slice = 0.3;
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < na; i++) {
            double remaining = until - now();
            if (remaining < 0.2) break;
            Cand *c = &all[i];
            if ((long)c->N <= bestN) continue;
            if (2L * c->N > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestN = N;
                bestc = *c;
                memcpy(bS, S, sizeof(int) * (size_t)d);
            }
        }
        if (until - now() < 0.2) break;
    }
    if (!have) return 0;
    if (!apply_cand(&bestc)) return 0;
    memcpy(S, bS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    if (cost_now() != 0) return 0;
    load_phase1();
    return 1;
}

/* ------------------------------------------------------------------ phase 2 */

/* Insert two vertices (An on side A, Bn on side B) by rewiring a random matching of d edges. */
static int try_insert(void) {
    int ea[MAXDEG], eb[MAXDEG];
    int cnt = 0, attempts = 0;
    markt++;
    while (cnt < d && attempts < 400) {
        attempts++;
        int v = rndint(V);
        if (deg[v] == 0) continue;
        int u = adj[v][rndint(deg[v])];
        int a = (side[v] == 0) ? v : u;
        int b = (side[v] == 0) ? u : v;
        if (mark[a] == markt || mark[b] == markt) continue;
        mark[a] = markt;
        mark[b] = markt;
        ea[cnt] = a;
        eb[cnt] = b;
        cnt++;
    }
    if (cnt < d) return 0;

    int An = V, Bn = V + 1;
    for (int i = 0; i < d; i++) {
        repl(adj[ea[i]], deg[ea[i]], eb[i], Bn);
        repl(adj[eb[i]], deg[eb[i]], ea[i], An);
    }
    for (int i = 0; i < d; i++) {
        adj[An][i] = eb[i];
        adj[Bn][i] = ea[i];
    }
    side[An] = 0;
    side[Bn] = 1;
    deg[An] = d;
    deg[Bn] = d;
    V += 2;
    if (check_valid()) return 1;

    V -= 2;
    for (int i = 0; i < d; i++) {
        repl(adj[ea[i]], deg[ea[i]], Bn, eb[i]);
        repl(adj[eb[i]], deg[eb[i]], An, ea[i]);
    }
    deg[An] = 0;
    deg[Bn] = 0;
    return 0;
}

static int pick_side(int s) {
    for (int t = 0; t < 1000; t++) {
        int v = rndint(V);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Random double-edge swap on the bipartite graph; kept only if still valid. */
static int try_swap(void) {
    int a1 = pick_side(0), a2 = pick_side(0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = adj[a1][rndint(deg[a1])];
    int b2 = adj[a2][rndint(deg[a2])];
    if (b1 == b2) return 0;
    if (has_nb(adj[a1], deg[a1], b2) || has_nb(adj[a2], deg[a2], b1)) return 0;

    repl(adj[a1], deg[a1], b1, b2);
    repl(adj[b1], deg[b1], a1, a2);
    repl(adj[a2], deg[a2], b2, b1);
    repl(adj[b2], deg[b2], a2, a1);
    if (check_valid()) return 1;

    repl(adj[a1], deg[a1], b2, b1);
    repl(adj[b1], deg[b1], a2, a1);
    repl(adj[a2], deg[a2], b1, b2);
    repl(adj[b2], deg[b2], a1, a2);
    return 0;
}

static void phase2(double until, long moore) {
    while (now() < until) {
        if ((long)V >= moore) break;
        if (V + 2 <= MAXV && try_insert()) continue;
        try_swap();
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 4970;
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    double t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    int in_state = load_stdin();
    if (in_state < 0) { print_complete(); return 0; }
    if (in_state == 0) {
        double t1 = t0 + usable * 0.35;
        if (!phase1(t1, ref)) { print_complete(); return 0; }
    }
    if (!check_valid()) { print_complete(); return 0; }

    phase2(t_end, moore);

    if (!check_valid()) { print_complete(); return 0; }
    print_graph();
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    best = start if start is not None else lib.haar_graph(d, range(d))  # K_{d,d}
    if best[0] >= lib.moore_bound(d, D):
        return best   # a Moore graph cannot be beaten
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        ref = REF_VERTICES.get((d, D), 4970)
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref],
                         stdin_graph=start, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best

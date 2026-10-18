"""Mixed bi-Cayley lift search for the weakest parent case (d=11, D=5).

Change from the parent: lifts are no longer only over metacyclic groups. Each round
either samples a permutation group (a random subgroup of PSL(2,q) or PGL(2,q) for a
prime q <= 31, acting on the q+1 projective points) or uses the parent's metacyclic
group. The group is used as a bi-Cayley lift: dart (i -> j, g) joins (i,x) to (j,x*g).
Left translation by G is an automorphism, so the diameter test needs only the 2p BFS
balls from the orbit representatives. Simulated annealing chooses the dart elements.

Python keeps a validated fallback (K_{d,d} or a Moore graph when one exists) and
only accepts a C result that is larger and passes lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Mixed lift search for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" + m edges of a valid start graph, or "0 0".
 * stdout: "n m" + edges of the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXDART (MAXD * MAXP)
#define MAXG 16384
#define PMAX 32
#define HSIZE 65536

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    size_t sz = (size_t)n * W;
    uint64_t *cur = malloc(sizeof(uint64_t) * sz);
    uint64_t *nxt = malloc(sizeof(uint64_t) * sz);
    if (!cur || !nxt) { free(cur); free(nxt); return 1; }
    memset(cur, 0, sizeof(uint64_t) * sz);
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
        total += n - c;
    }
    free(cur);
    free(nxt);
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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

/* ------------------------------------------------------------ group state */

enum { GK_META = 0, GK_PERM = 1 };
static int gkind = GK_META;
static int gN = 0;
static int gmod = 1, gk = 1;          /* META: Z_gmod x| Z_gk */
static int grp_rp[MAXG];              /* META: r^b mod gmod */
static int invt[MAXG];                /* inverse index of each element */
static unsigned char pel[MAXG][PMAX]; /* PERM: element permutations */
static int pdeg = 0;
static int phash[HSIZE];              /* open addressing, stores index+1 */

static unsigned perm_hash(const unsigned char *p) {
    unsigned h = 2166136261u;
    for (int i = 0; i < pdeg; i++) { h ^= p[i]; h *= 16777619u; }
    return h & (HSIZE - 1);
}

static int perm_find(const unsigned char *p) {
    unsigned h = perm_hash(p);
    for (;;) {
        int e = phash[h];
        if (e == 0) return -1;
        if (memcmp(pel[e - 1], p, pdeg) == 0) return e - 1;
        h = (h + 1) & (HSIZE - 1);
    }
}

static void perm_insert(int idx) {
    unsigned h = perm_hash(pel[idx]);
    while (phash[h]) h = (h + 1) & (HSIZE - 1);
    phash[h] = idx + 1;
}

/* Closure of the generators under right multiplication, starting from the identity.
 * Returns the group order, or 0 if it would exceed limit. */
static int perm_closure(unsigned char gens[][PMAX], int ng, int dg, int limit) {
    pdeg = dg;
    memset(phash, 0, sizeof phash);
    memset(pel[0], 0, PMAX);
    for (int i = 0; i < dg; i++) pel[0][i] = (unsigned char)i;
    perm_insert(0);
    int n = 1;
    unsigned char c[PMAX];
    for (int head = 0; head < n; head++) {
        for (int s = 0; s < ng; s++) {
            memset(c, 0, PMAX);
            for (int i = 0; i < dg; i++) c[i] = pel[head][gens[s][i]];
            if (perm_find(c) >= 0) continue;
            if (n >= limit) return 0;
            memcpy(pel[n], c, PMAX);
            perm_insert(n);
            n++;
        }
    }
    return n;
}

static int meta_mul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int first = (int)(((long)a + (long)grp_rp[b] * c) % gmod);
    return first * gk + (b + e) % gk;
}

/* Right multiplication x * y in the current group. */
static int grmul(int x, int y) {
    if (gkind == GK_META) return meta_mul(x, y);
    unsigned char c[PMAX];
    memset(c, 0, PMAX);
    for (int i = 0; i < pdeg; i++) c[i] = pel[x][pel[y][i]];
    return perm_find(c);
}

/* Random metacyclic group Z_m x| Z_k of order N (parent's construction). */
static int random_meta(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    gkind = GK_META;
    gN = N;
    gmod = bm;
    gk = bk;
    grp_rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) grp_rp[b] = (int)((long)grp_rp[b - 1] * br % bm);
    for (int x = 0; x < N; x++) {
        int a = x / bk, b = x - a * bk;
        int e = (bk - b) % bk;
        long c = ((long)(bm - a) % bm) * grp_rp[e] % bm;
        invt[x] = (int)c * bk + e;
    }
    return 1;
}

/* ------------------------------------------------------------ ambient PSL/PGL(2,q) */

typedef struct {
    unsigned char g[2][PMAX];
    int ng, dg, q, p, N;
} PChoice;

static const int QS[] = {5, 7, 11, 13, 17, 19, 23, 29, 31};
#define NQ 9

/* Mobius map x -> (a x + b)/(c x + dd) on the projective line {0..q-1, q=infinity}. */
static void mob(int q, long a, long b, long c, long dd, unsigned char *out) {
    for (int x = 0; x <= q; x++) {
        long img;
        if (x == q) {
            img = (c % q == 0) ? q : (a % q) * powmod(c % q, q - 2, q) % q;
        } else {
            long nu = ((a * x + b) % q + q) % q;
            long de = ((c * x + dd) % q + q) % q;
            img = (de == 0) ? q : nu * powmod(de, q - 2, q) % q;
        }
        out[x] = (unsigned char)img;
    }
}

static int nonsquare(int q) {
    for (int s = 2; s < q; s++)
        if (powmod(s, (q - 1) / 2, q) == q - 1) return s;
    return 1;
}

/* Generators of PSL(2,q) (pgl = 0) or PGL(2,q) (pgl = 1). */
static void build_ambient(int q, int pgl, unsigned char amb[3][PMAX]) {
    int s = pgl ? nonsquare(q) : 4;
    mob(q, 1, 1, 0, 1, amb[0]);          /* x -> x + 1 */
    mob(q, 0, q - 1, 1, 0, amb[1]);      /* x -> -1/x */
    mob(q, s, 0, 0, 1, amb[2]);          /* x -> s x */
}

/* Random element as a random word of length L in the three ambient generators. */
static void random_elem(unsigned char amb[3][PMAX], int dg, int L, unsigned char *out) {
    unsigned char e[PMAX], c[PMAX];
    memset(e, 0, PMAX);
    for (int i = 0; i < dg; i++) e[i] = (unsigned char)i;
    for (int s = 0; s < L; s++) {
        int g = rndint(3);
        memset(c, 0, PMAX);
        for (int i = 0; i < dg; i++) c[i] = e[amb[g][i]];
        memcpy(e, c, PMAX);
    }
    memcpy(out, e, PMAX);
}

/* Sample random 1- or 2-generated subgroups; keep the one whose lift order
 * v = 2pN is the smallest value in (lo, min(hi, lo+cap)]. */
static int pick_perm(long lo, long hi, long cap, PChoice *pc) {
    long bestv = 0;
    unsigned char amb[3][PMAX];
    for (int tr = 0; tr < 60 && now() < t_end; tr++) {
        int q = QS[rndint(NQ)];
        int pgl = rndint(2);
        int dg = q + 1;
        build_ambient(q, pgl, amb);
        int ng = 1 + rndint(2);
        unsigned char gens[2][PMAX];
        memset(gens, 0, sizeof gens);
        for (int k = 0; k < ng; k++) random_elem(amb, dg, 30, gens[k]);
        long limit = hi / 2;
        if (limit > MAXG) limit = MAXG;
        int N = perm_closure(gens, ng, dg, (int)limit);
        if (N < 2) continue;
        for (int p = 1; p <= 2; p++) {
            long v = 2L * p * N;
            if (v <= lo || v > hi || v > lo + cap) continue;
            if (bestv == 0 || v < bestv) {
                bestv = v;
                memcpy(pc->g, gens, sizeof gens);
                pc->ng = ng;
                pc->dg = dg;
                pc->q = q;
                pc->p = p;
                pc->N = N;
            }
        }
    }
    return bestv != 0;
}

/* Rebuild the chosen permutation group and its inverse table. */
static int setup_perm(PChoice *pc) {
    int N = perm_closure(pc->g, pc->ng, pc->dg, MAXG);
    if (N < 2 || N != pc->N) return 0;
    gkind = GK_PERM;
    gN = N;
    for (int x = 0; x < N; x++) {
        unsigned char iv[PMAX];
        memset(iv, 0, PMAX);
        for (int i = 0; i < pdeg; i++) iv[pel[x][i]] = (unsigned char)i;
        int y = perm_find(iv);
        if (y < 0) return 0;
        invt[x] = y;
    }
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley lifts */

static int gP, gV;
static int nd;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART], dGi[MAXDART];
static int rowD[MAXP][MAXD], colD[MAXP][MAXD];
static int tabF[MAXDART][MAXN], tabB[MAXDART][MAXN];

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP], stack[2 * MAXP], top = 0, nseen = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = (v < p) ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static int dart_clash(int i, int j, int g, int skip) {
    for (int t = 0; t < nd; t++)
        if (t != skip && dI[t] == i && dJ[t] == j && dG[t] == g) return 1;
    return 0;
}

static void rebuild_rows(void) {
    int rc[MAXP] = {0}, cc[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        rowD[dI[t]][rc[dI[t]]++] = t;
        colD[dJ[t]][cc[dJ[t]]++] = t;
    }
}

static void set_dart_table(int t) {
    for (int x = 0; x < gN; x++) tabF[t][x] = grmul(x, dG[t]);
    for (int x = 0; x < gN; x++) tabB[t][tabF[t][x]] = x;   /* inverse map */
}

/* Number of vertices within distance D of source s. */
static int bfs_reach(int s) {
    static int q[MAXN];
    static int vis[MAXN];
    static int stamp = 0;
    stamp++;
    if (stamp == 0x7fffffff) { memset(vis, 0, sizeof vis); stamp = 1; }
    const int N = gN, PN = gP * gN;
    int head = 0, tail = 0;
    q[tail++] = s;
    vis[s] = stamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = q[head++];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int c = 0; c < d; c++) {
                    int t = rowD[i][c];
                    int w = PN + dJ[t] * N + tabF[t][x];
                    if (vis[w] != stamp) { vis[w] = stamp; q[tail++] = w; }
                }
            } else {
                int u = v - PN, j = u / N, y = u - j * N;
                for (int c = 0; c < d; c++) {
                    int t = colD[j][c];
                    int w = dI[t] * N + tabB[t][y];
                    if (vis[w] != stamp) { vis[w] = stamp; q[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (representative, vertex) pairs. Zero means diameter <= D, by left-translation. */
static long eval_cost(void) {
    long cost = 0;
    for (int i = 0; i < gP; i++) {
        cost += gV - bfs_reach(i * gN);
        cost += gV - bfs_reach(gP * gN + i * gN);
    }
    return cost;
}

/* Anneal dart group elements of one random base over the current group. */
static int attempt(int p, long maxEval, Graph *out) {
    int M[MAXP][MAXP];
    const int N = gN;
    if (N < d || 2L * p * N > MAXN) return 0;
    gP = p;
    gV = 2 * p * N;
    make_base(p, M);
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                int g;
                do { g = rndint(N); } while (dart_clash(i, j, g, -1));
                dI[nd] = i; dJ[nd] = j; dG[nd] = g; dGi[nd] = invt[g];
                nd++;
            }
    for (int t = 0; t < nd; t++) set_dart_table(t);
    rebuild_rows();
    long cost = eval_cost();
    double T = 2.0;
    for (long it = 0; it < maxEval && cost > 0; it++) {
        if ((it & 15) == 0 && now() > t_end) break;
        int t = rndint(nd);
        int g;
        do { g = rndint(N); } while (dart_clash(dI[t], dJ[t], g, t));
        int og = dG[t], ogi = dGi[t];
        dG[t] = g;
        dGi[t] = invt[g];
        set_dart_table(t);
        long nc = eval_cost();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
        else {
            dG[t] = og;
            dGi[t] = ogi;
            set_dart_table(t);
        }
        T *= 0.9995;
        if (T < 0.2) T = 2.0;
    }
    if (cost != 0) return 0;
    out->n = gV;
    for (int v = 0; v < gV; v++) { out->deg[v] = 0; out->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(out, dI[t] * N + x, p * N + dJ[t] * N + tabF[t][x]);
    return is_valid(out);
}

/* Parent-style metacyclic step aiming at order lo + delta. */
static int meta_step(long lo, long delta, long moore, Graph *out) {
    long target = lo + delta;
    int p = 1 + rndint(3);
    long N = (target + 2L * p - 1) / (2L * p);
    if (N < d + 1) N = d + 1;
    if (2L * p * N > moore) {
        p = 1;
        N = (target + 1) / 2;
        if (N < d + 1) N = d + 1;
        if (2L * N > moore) return 0;
    }
    if (!random_meta((int)N)) return 0;
    long V = 2L * p * N;
    long ops = 2L * p * V * d;
    long maxEval = (long)(6.0e8 / (double)ops);
    if (maxEval < 300) maxEval = 300;
    return attempt(p, maxEval, out);
}

static void search(Graph *best) {
    static Graph cand;
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    long delta = best->n / 10 > 2 ? best->n / 10 : 2;
    int fails = 0;
    while (now() < t_end) {
        long lo = best->n;
        long room = moore - lo;
        if (room < 2) break;
        if (delta > room) delta = room;
        if (delta < 2) delta = 2;
        int ok = 0;
        PChoice pc;
        if ((rnd() % 4) != 0 && pick_perm(lo, moore, 4 * delta, &pc)) {
            if (setup_perm(&pc)) {
                long V = 2L * pc.p * pc.N;
                long ops = 2L * V * d;
                long maxEval = (long)(6.0e8 / (double)ops);
                if (maxEval < 300) maxEval = 300;
                ok = attempt(pc.p, maxEval, &cand);
            }
        } else {
            ok = meta_step(lo, delta, moore, &cand);
        }
        if (ok && cand.n > best->n) {
            copy_graph(best, &cand);
            fails = 0;
            delta = best->n / 10 > 2 ? best->n / 10 : 2;
        } else if (++fails % 4 == 0 && delta > 2) {
            delta /= 2;
        }
    }
}

/* ------------------------------------------------------------ main */

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
    if (D < 2 || d < 1 || d > MAXD) {
        printf("2 1\n0 1\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore_bound()) search(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Safe fallback: a single edge is valid for any D >= 1 and d >= 1.
    best = (2, [(0, 1)])

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None

    candidates = []
    if start is not None:
        candidates.append(start)
    candidates.append(lib.haar_graph(d, range(d)))   # K_{d,d}, valid for D >= 2
    for n, edges in candidates:
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    budget = 0.9 * time_limit - 2.0 - (time.monotonic() - t0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine

    if budget > 0.5 and D >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 8.0)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass   # keep the valid fallback

    return best

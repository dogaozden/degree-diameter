"""Multi-fibre voltage-lift annealing followed by greedy-endpoint growth, for the d=5, D=7 target.

This revision replaces the bi-Cayley-first search with a different construction. Vertex set:
A-fibres i = 0..p-1 and B-fibres j = 0..p-1, each a copy of a group G = Z_m x| Z_k of order N.
A base multigraph is d-regular and bipartite on p+p vertices. Dart (i, j, g) joins
A(i, x) to B(j, x*g) for all x, so the lift is d-regular and bipartite with 2pN vertices.
Left multiplication by G is an automorphism that is transitive on each fibre, so the diameter
check needs one BFS per fibre (2p BFS in total). The objective is the number of unreached
(source, vertex) pairs. Voltages are annealed at p in {2, 3, 4} and N chosen so that 2pN exceeds
the incumbent. Lifts are only accepted after lib-style validation in C.

If the lift phase finds nothing, or after it, the incumbent is grown by greedy-endpoint pair
insertion with annealing and ruin-and-recreate. Each candidate is checked in C with a full
bitset diameter test and again in Python with lib.is_valid. The algebraic starts (Hexagon
H(q), projective planes, W(q), Araujo-Lopez) remain as fallbacks, so every case returns a valid graph.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre voltage-lift annealer, then greedy-endpoint growth.
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
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXG 1024
#define MAXDART (MAXD * MAXP)
#define GREEDY_CAND 24
#define INIT_TRIALS 4
#define LIFT_STEPS 20000
#define LIFT_ATT 3

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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* ---------------- groups: Z_m x|_r Z_k, element a*k + b ---------------- */

typedef struct {
    int m, k, r;
    int rp[MAXG];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
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

/* Prefer a non-abelian choice (r != 1, k > 1) when one is sampled quickly. */
static int pick_group(int N, Grp *G) {
    for (int t = 0; t < 6; t++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

/* ---------------- multi-fibre voltage lifts ----------------
 * A(i, x) = i*N + x, B(j, y) = (P + j)*N + y.
 * Dart t = (dI, dJ, dG) gives A(dI, x) -- B(dJ, x * dG) for all x.
 * Every A fibre and every B fibre carries exactly d darts. */

static int LP, LN;
static int MT[MAXG * MAXG];
static int INVT[MAXG];
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART], dGI[MAXDART];
static int ndart;
static int dA[MAXP][MAXD], dB[MAXP][MAXD];
static int cntA[MAXP], cntB[MAXP];
static int stampL[MAXN], distL[MAXN], qL[MAXN];
static int lstamp = 0;

static void setup_mult(const Grp *G, int N) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INVT[x] = y; break; }
}

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Fresh random base and voltages for p fibres over the current group. */
static void init_darts(int p) {
    int M[MAXP][MAXP];
    make_base(p, M);
    ndart = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++) {
            int first = ndart;
            for (int c = 0; c < M[i][j]; c++) {
                int t = ndart++;
                dI[t] = i;
                dJ[t] = j;
                int g;
                for (;;) {
                    g = rndint(LN);
                    int clash = 0;
                    for (int u = first; u < t; u++)
                        if (dG[u] == g) { clash = 1; break; }
                    if (!clash) break;
                }
                dG[t] = g;
                dGI[t] = INVT[g];
            }
        }
    for (int i = 0; i < p; i++) { cntA[i] = 0; cntB[i] = 0; }
    for (int t = 0; t < ndart; t++) {
        dA[dI[t]][cntA[dI[t]]++] = t;
        dB[dJ[t]][cntB[dJ[t]]++] = t;
    }
}

/* Number of (fibre representative, vertex) pairs at distance > D, one source per fibre. */
static long lift_bad(void) {
    int N = LN, P = LP;
    int V = 2 * P * N;
    long total = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = s * N;
        lstamp++;
        int head = 0, tail = 0;
        stampL[src] = lstamp;
        distL[src] = 0;
        qL[tail++] = src;
        while (head < tail) {
            int v = qL[head++];
            int dv = distL[v];
            if (dv >= D) continue;
            if (v < P * N) {
                int i = v / N, x = v % N;
                for (int t = 0; t < d; t++) {
                    int dt = dA[i][t];
                    int u = (P + dJ[dt]) * N + MT[x * N + dG[dt]];
                    if (stampL[u] != lstamp) {
                        stampL[u] = lstamp;
                        distL[u] = dv + 1;
                        qL[tail++] = u;
                    }
                }
            } else {
                int off = v - P * N;
                int jj = off / N, y = off % N;
                for (int t = 0; t < d; t++) {
                    int dt = dB[jj][t];
                    int u = dI[dt] * N + MT[y * N + dGI[dt]];
                    if (stampL[u] != lstamp) {
                        stampL[u] = lstamp;
                        distL[u] = dv + 1;
                        qL[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static void lift_fill(Graph *g) {
    int N = LN, P = LP;
    g->n = 2 * P * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= P * N; }
    for (int t = 0; t < ndart; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (P + dJ[t]) * N + MT[x * N + dG[t]]);
}

/* Annealed voltage search for the current darts. Returns the best objective seen and
 * leaves the best voltages in place. */
static long lift_anneal(long steps, double until) {
    static int bestG[MAXDART];
    long bad = lift_bad();
    long bestb = bad;
    memcpy(bestG, dG, sizeof(int) * ndart);
    double T = 4.0;
    double alpha = pow(0.05, 1.0 / (double)steps);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(ndart);
        int old = dG[t];
        int ng;
        for (;;) {
            ng = rndint(LN);
            int clash = 0;
            for (int u = 0; u < ndart; u++)
                if (u != t && dI[u] == dI[t] && dJ[u] == dJ[t] && dG[u] == ng) { clash = 1; break; }
            if (!clash) break;
        }
        dG[t] = ng;
        dGI[t] = INVT[ng];
        long nb = lift_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(bestG, dG, sizeof(int) * ndart);
            }
        } else {
            dG[t] = old;
            dGI[t] = INVT[old];
        }
        T *= alpha;
        if (T < 0.05) T = 0.05;
    }
    memcpy(dG, bestG, sizeof(int) * ndart);
    for (int t = 0; t < ndart; t++) dGI[t] = INVT[dG[t]];
    return bestb;
}

/* Search lifts of order 2pN strictly above the incumbent, for p in {2,3,4}. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    static const int plist[3] = {2, 3, 4};
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    while (now() < until) {
        long target = best->n + 2;
        if (target > cap) return;
        int p = plist[rndint(3)];
        long Nmin = (target + 2L * p - 1) / (2L * p);
        long N = Nmin + rndint(3);
        if (2L * p * Nmin > cap || Nmin > MAXG) continue;
        if (2L * p * N > cap || N > MAXG) N = Nmin;
        if (!pick_group((int)N, &G)) continue;
        setup_mult(&G, (int)N);
        LP = p;
        LN = (int)N;
        for (int a = 0; a < LIFT_ATT && now() < until; a++) {
            init_darts(p);
            long b = lift_anneal(LIFT_STEPS, until);
            if (b == 0) {
                lift_fill(&cand);
                if (cand.n > best->n && is_valid(&cand)) {
                    copy_graph(best, &cand);
                    break;
                }
            }
        }
    }
}

/* ---------------- greedy endpoint growth ---------------- */

/* Random wiring of one new vertex pair x (side 0), y (side 1) onto best (fallback). */
static void wire_pair(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
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
}

static int bq_dist[MAXN], bq_queue[MAXN], bq_mark[MAXN];
static int bq_stamp = 0;

/* Number of vertices within distance D of src (src included). */
static int ball_size(const Graph *g, int src) {
    int head = 0, tail = 0;
    bq_stamp++;
    bq_mark[src] = bq_stamp;
    bq_dist[src] = 0;
    bq_queue[tail++] = src;
    while (head < tail) {
        int v = bq_queue[head++];
        if (bq_dist[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (bq_mark[u] != bq_stamp) {
                bq_mark[u] = bq_stamp;
                bq_dist[u] = bq_dist[v] + 1;
                bq_queue[tail++] = u;
            }
        }
    }
    return tail;
}

/* Greedy endpoint-coverage wiring of the new pair x (side 0), y (side 1). */
static int wire_greedy(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0; k < d - 1; k++) {
        int ba = -1, bb = -1;
        long bscore = -1;
        int got = 0;
        for (int att = 0; got < GREEDY_CAND && att < 4000; att++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            got++;
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            long score = (long)(work->n - ball_size(work, x)) +
                         (long)(work->n - ball_size(work, y)) +
                         (long)(work->n - ball_size(work, a)) +
                         (long)(work->n - ball_size(work, b));
            del_edge(work, x, b);
            del_edge(work, y, a);
            add_edge(work, a, b);
            if (bscore < 0 || score < bscore) { bscore = score; ba = a; bb = b; }
        }
        if (ba < 0) return 0;
        del_edge(work, ba, bb);
        add_edge(work, x, bb);
        add_edge(work, y, ba);
        used[ba] = used[bb] = stamp;
    }
    return 1;
}

/* Grow best by one vertex pair: pick the best of INIT_TRIALS wirings, then anneal. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    static Graph trial;
    long bestbad = -1;
    for (int t = 0; t < INIT_TRIALS; t++) {
        if (!wire_greedy(best, &trial)) wire_pair(best, &trial);
        long b = bad_pairs(&trial);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &trial);
        }
        if (bestbad == 0 || now() > until) break;
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

/* ---------------- ruin and recreate ----------------
 * Remove a BFS ball holding k A-vertices and k B-vertices, refill the freed degree slots with
 * random new A-B edges, then regrow k+1 pairs with grow_once. */

static Graph rr_cur, rr_nxt;
static int rr_ball[MAXN], rr_mark[MAXN], rr_map[MAXN];
static unsigned char rr_rem[MAXN];

static void deficit_fill(Graph *g) {
    int n = g->n;
    if (n < 2) return;
    for (long it = 0; it < 40L * n; it++) {
        int a = rndint(n), b = rndint(n);
        if (g->side[a] != 0 || g->side[b] != 1) continue;
        if (g->deg[a] >= d || g->deg[b] >= d || has_edge(g, a, b)) continue;
        add_edge(g, a, b);
    }
}

static int ruin_recreate(const Graph *best, Graph *out, int k, double until) {
    int n = best->n;
    if (k < 1 || n < 2 * k + 4 || n > MAXN - 2) return 0;
    int v0 = rndint(n);
    for (int i = 0; i < n; i++) { rr_mark[i] = 0; rr_rem[i] = 0; }
    int head = 0, tail = 0;
    rr_mark[v0] = 1;
    rr_ball[tail++] = v0;
    while (head < tail && tail < 6 * k + 6) {
        int v = rr_ball[head++];
        for (int i = 0; i < best->deg[v]; i++) {
            int u = best->adj[v][i];
            if (!rr_mark[u]) { rr_mark[u] = 1; rr_ball[tail++] = u; }
        }
    }
    int ra = 0, rb = 0;
    for (int i = 0; i < tail; i++) {
        int v = rr_ball[i];
        if (best->side[v] == 0) {
            if (ra < k) { rr_rem[v] = 1; ra++; }
        } else if (rb < k) {
            rr_rem[v] = 1;
            rb++;
        }
    }
    if (ra < k || rb < k) return 0;

    int m = 0;
    for (int v = 0; v < n; v++) rr_map[v] = rr_rem[v] ? -1 : m++;
    out->n = m;
    for (int v = 0; v < n; v++) {
        if (rr_map[v] < 0) continue;
        out->deg[rr_map[v]] = 0;
        out->side[rr_map[v]] = best->side[v];
    }
    for (int v = 0; v < n; v++) {
        if (rr_map[v] < 0) continue;
        for (int i = 0; i < best->deg[v]; i++) {
            int u = best->adj[v][i];
            if (u > v && rr_map[u] >= 0) add_edge(out, rr_map[v], rr_map[u]);
        }
    }
    deficit_fill(out);

    copy_graph(&rr_cur, out);
    for (int s = 0; s <= k; s++) {
        if (now() > until) return 0;
        if (rr_cur.n + 2 > moore_bound() || rr_cur.n + 2 > MAXN) return 0;
        if (!grow_once(&rr_cur, &rr_nxt, until)) return 0;
        copy_graph(&rr_cur, &rr_nxt);
    }
    copy_graph(out, &rr_cur);
    return is_valid(out);
}

static void grow_search(Graph *best, double until) {
    static Graph work, rr;
    int fails = 0;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) {
            copy_graph(best, &work);
            fails = 0;
            continue;
        }
        fails++;
        if (fails % 2 == 0 && now() < until) {
            int k = 2 + rndint(3);
            double rslice = now() + slice;
            if (rslice > until) rslice = until;
            if (ruin_recreate(best, &rr, k, rslice) && rr.n > best->n) copy_graph(best, &rr);
        }
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double L = t_end - t0;
    if (D >= 2 && d >= 3 && best.n < moore_bound()) lift_search(&best, t0 + L * 0.5);
    if (D >= 2 && best.n < moore_bound()) grow_search(&best, t_end);
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            try:
                out.append(_gq_w(q))
            except Exception:
                pass
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
        try:
            n, e = cand
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

"""Combined program: a C engine runs successive-halving bi-Cayley lift search over
semidirect groups Z_m x| Z_k2, then grow-by-two insertion from the best graph. Python
supplies the exact baselines (projective planes, generalized quadrangles, Araujo-Pardo
and Lopez graphs), K_{d,d} as a fallback, and a slack extension. Every returned graph is
checked with lib.is_valid.
"""
import itertools
import random
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
#define MAXD 64
#define MAXW (MAXN / 64)
#define CANDS 6
#define MAXK 8
#define PENALTY 1000
#define POOL 12

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static double t_end;
static Graph gbest, gwork, gtry, gcand;
static int used[MAXN];
static int stamp = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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

static void make_kdd(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < 2 * d; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v < d ? 0 : 1);
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            add_edge(g, a, d + b);
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

/* ---------------- grow-by-two insertion ---------------- */

/* Insert x (side 0) and y (side 1) joined by an edge, stealing d-1 disjoint edges. */
static void make_candidate(const Graph *best, Graph *w) {
    int n = best->n;
    copy_graph(w, best);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

static void choose_candidate(const Graph *best, Graph *work) {
    long bestbad = -1;
    for (int c = 0; c < CANDS; c++) {
        make_candidate(best, &gtry);
        long b = bad_pairs(&gtry);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &gtry);
        }
        if (b == 0) break;
    }
}

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    choose_candidate(best, work);
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

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound() && gbest.n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
    }
}

/* ---------------- bi-Cayley lift search ---------------- */

typedef struct {
    int m, k2;
    long long r;
    int pw[64];
    int G;
} Group;
static Group grp;

static void set_group(int m, int k2, long long r) {
    grp.m = m;
    grp.k2 = k2;
    grp.G = m * k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        grp.pw[b] = (int)p;
        p = (p * r) % m;
    }
}

/* Element a*k2+b; (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + (long long)grp.pw[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = ((long long)grp.pw[nb] * a) % m;
    long long na = (m - t) % m;
    return (int)(na * k2 + nb);
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

typedef struct {
    int m, k2, K, ord;
    long long r;
    int layers[MAXD][MAXK];
    int S[MAXD][MAXK];
    long long cost;
    double c0;
    long steps;
    long Tmax;
} Cand;

static int K, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr = NULL;          /* nbr[l*N + v] */
static uint64_t *la = NULL, *lb = NULL;
static long capN = 0;
static uint64_t FULL;

static void ensure_capacity(long n) {
    if (n <= capN) return;
    free(nbr);
    free(la);
    free(lb);
    capN = n + n / 4 + 16;
    nbr = malloc(sizeof(int) * (size_t)d * (size_t)capN);
    la = malloc(sizeof(uint64_t) * (size_t)capN);
    lb = malloc(sizeof(uint64_t) * (size_t)capN);
    if (!nbr || !la || !lb) {
        print_graph(&gbest);
        exit(0);
    }
}

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int sinv = ginv(s);
    int *nl = nbr + (size_t)l * N;
    int q = K + p;
    for (int g = 0; g < G; g++) nl[i * G + g] = q * G + gmul(g, s);
    for (int h = 0; h < G; h++) nl[q * G + h] = i * G + gmul(h, sinv);
}

static int reach_eval(void) {
    for (int v = 0; v < N; v++) la[v] = 0;
    for (int b = 0; b < 2 * K; b++) la[b * G] |= (uint64_t)1 << b;
    for (int round = 0; round < D; round++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t u = la[v];
            for (int l = 0; l < d; l++) u |= la[nbr[(size_t)l * N + v]];
            lb[v] = u;
            if (u != la[v]) changed = 1;
        }
        uint64_t *t = la;
        la = lb;
        lb = t;
        if (!changed) break;
    }
    int unr = 0;
    for (int v = 0; v < N; v++) unr += pc64(FULL & ~la[v]);
    return unr;
}

static long long eval_cost(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    int unr = reach_eval();
    return (long long)unr + (long long)PENALTY * dup;
}

/* Convert the current zero-cost lift into a Graph and keep it if valid and larger. */
static void record_solution(void) {
    if (N > MAXN || N <= gbest.n) return;
    gcand.n = N;
    for (int v = 0; v < N; v++) {
        gcand.deg[v] = 0;
        gcand.side[v] = (unsigned char)(v >= K * G ? 1 : 0);
    }
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++)
            add_edge(&gcand, u, nbr[(size_t)l * N + u]);
    if (is_valid(&gcand)) copy_graph(&gbest, &gcand);
}

static long long cand_load(const Cand *c) {
    set_group(c->m, c->k2, c->r);
    K = c->K;
    G = grp.G;
    N = 2 * K * G;
    FULL = (((uint64_t)1) << (2 * K)) - 1;
    ensure_capacity(N);
    memcpy(layers, c->layers, sizeof(layers));
    memcpy(S, c->S, sizeof(S));
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
    return eval_cost();
}

static void cand_save(Cand *c) {
    memcpy(c->layers, layers, sizeof(layers));
    memcpy(c->S, S, sizeof(S));
}

/* Anneal from the loaded state for up to `steps` moves. */
static long long anneal_run(long long cost, double c0, long steps, long step0,
                            long Tmax, double deadline, long *done) {
    *done = 0;
    for (long t = 0; t < steps; t++) {
        if (cost == 0) break;
        if (now() > deadline) break;
        (*done)++;
        long gt = step0 + t;
        double temp = 0.5;
        if (gt < Tmax) temp = 0.01 * c0 * (1.0 - (double)gt / (double)Tmax);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            for (int tries = 0; tries < 30 && l < 0; tries++) {
                int v = rndint(N);
                if ((la[v] & FULL) != FULL) {
                    int block = v / G;
                    if (block < K) {
                        i = block;
                        l = rndint(d);
                    } else {
                        int ll = rndint(d);
                        for (int j = 0; j < K; j++)
                            if (layers[ll][j] == block - K) { i = j; l = ll; break; }
                    }
                }
            }
        }
        if (l < 0) {
            l = rndint(d);
            i = rndint(K);
        }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost;
}

static const int K2LIST[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, int *pm, int *pk2, long long *pr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2LIST[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
        } else {
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    long long c = 2 + rndint(m - 2);
                    if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            } else {
                r = 1;
            }
            if (r < 0) continue;
        }
        *pm = m;
        *pk2 = k2;
        *pr = r;
        return 1;
    }
    return 0;
}

static int choose_k(const long *trials, const long *wins) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    double bs = -1.0;
    int k = 1;
    for (int kk = 1; kk <= MAXK; kk++) {
        double s = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; k = kk; }
    }
    return k;
}

/* Random candidate lift of base size k with order above bn (and within MAXN). */
static int gen_cand(Cand *c, int k, int bn) {
    int base = bn / (2 * k);
    int spread = base / 8 + 1;
    int target = base + 1 + rndint(spread);
    if (target < 2) target = 2;
    int m, k2;
    long long r;
    if (!sample_group(target, &m, &k2, &r)) return 0;
    set_group(m, k2, r);
    long long Gl = grp.G;
    long long NN = 2LL * k * Gl;
    if (NN <= bn || NN > MAXN) return 0;
    c->m = m;
    c->k2 = k2;
    c->r = r;
    c->K = k;
    c->ord = (int)NN;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) c->layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = c->layers[l][i];
            c->layers[l][i] = c->layers[l][j];
            c->layers[l][j] = tmp;
        }
        for (int i = 0; i < k; i++) c->S[l][i] = rndint((int)Gl);
    }
    c->Tmax = 8000 + 6 * (long)NN;
    c->steps = 0;
    c->cost = cand_load(c);
    c->c0 = c->cost > 1 ? (double)c->cost : 1.0;
    return 1;
}

/* Successive halving over pools of random lifts, until time `until`. */
static void lift_phase(double until) {
    static Cand pool[POOL];
    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    int fails = 0;
    while (now() < until) {
        int np = 0;
        for (int a = 0; a < 20 * POOL && np < POOL && now() < until; a++) {
            int k = choose_k(trials, wins);
            if (gen_cand(&pool[np], k, gbest.n)) {
                trials[k]++;
                np++;
            }
        }
        if (np == 0) {
            if (++fails > 200) break;
            continue;
        }
        fails = 0;

        long maxN = 0;
        for (int i = 0; i < np; i++)
            if (pool[i].ord > maxN) maxN = pool[i].ord;
        long s0 = 400 + maxN / 6;

        long B = s0;
        int alive = np, found = 0;
        while (alive > 0 && !found && now() < until) {
            for (int i = 0; i < alive && now() < until; i++) {
                Cand *c = &pool[i];
                long long cur = cand_load(c);
                long done = 0;
                long long cost = anneal_run(cur, c->c0, B, c->steps, c->Tmax, until, &done);
                c->steps += done;
                c->cost = cost;
                cand_save(c);
                if (cost == 0) {
                    record_solution();
                    wins[c->K]++;
                    found = 1;
                    break;
                }
            }
            if (found) break;

            for (int i = 1; i < alive; i++) {
                Cand tmp = pool[i];
                int j = i - 1;
                while (j >= 0 && pool[j].cost > tmp.cost) {
                    pool[j + 1] = pool[j];
                    j--;
                }
                pool[j + 1] = tmp;
            }
            if (alive > 1) alive = (alive + 1) / 2;
            B *= 2;
            if (alive == 1 && B > 32 * s0) break;
        }
    }
}

/* ---------------- main ---------------- */

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double tl = atof(argv[4]);
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + tl - 1.0;
    if (t_end < t0 + 0.5) t_end = t0 + 0.5;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start(&gbest);
    if (gbest.n == 0) make_kdd(&gbest);

    lift_phase(t0 + 0.65 * (t_end - t0));
    grow_search(t_end);

    if (!is_valid(&gbest)) make_kdd(&gbest);
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Algebraic baselines.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Slack extension: add vertices using spare degree; every kept graph is valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    if D == 2:
        return best

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(*pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                try:
                    consider(*_gq_w(q))
                except Exception:
                    pass
                if q == d - 1 and best_n == 2 * (q + 1) * (q * q + 1):
                    return best
                break

    # Cheap slack extension on the algebraic baseline (bounded in time).
    rng = random.Random(seed)
    try:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng,
                               min(time.monotonic() + 3.0, t0 + 0.05 * time_limit))
        consider(n2, e2)
    except Exception:
        pass

    # Main engine: one C run doing lift search, then grow-by-two from the best graph.
    budget = max(2.0, 0.82 * time_limit - 2.0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best

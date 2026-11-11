import lib


C_LIFT = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 8
#define GMAX 2000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    G_ = G;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static void apply_dart(int l, int i) { setdart(l, i, lay[l][i], VS[l][i]); }

static void snapshot(void) {
    memcpy(BL, lay, sizeof lay);
    memcpy(BV, VS, sizeof VS);
}

static void restore_snapshot(void) {
    int d = d_, k = K_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) { lay[l][i] = BL[l][i]; VS[l][i] = BV[l][i]; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
}

/* Cost = unreached (representative, vertex) pairs + heavy penalty for duplicate darts. */
static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_, N = N_;
    u64 full = (1ULL << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    snapshot();
    int last = 0, kicks = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            restore_snapshot();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                VS[l][i] = rndi(G);
                apply_dart(l, i);
            }
            cost = evalcost();
            if (cost < bestc) { bestc = cost; snapshot(); }
            last = t;
            continue;
        }
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rndu() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            apply_dart(l, i1);
            apply_dart(l, i2);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                apply_dart(l, i1);
                apply_dart(l, i2);
            }
        } else {
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.4) {
                int start = rndi(N), v = -1;
                for (int q = 0; q < N; q++) {
                    int w = (start + q) % N;
                    if (rch[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndi(d);
                    if (b < k) i = b;
                    else {
                        int jb = b - k;
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == jb) { i = ii; break; }
                        if (i < 0) i = rndi(k);
                    }
                    picked = 1;
                }
            }
            if (!picked) { l = rndi(d); i = rndi(k); }
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            apply_dart(l, i);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                VS[l][i] = old;
                apply_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; snapshot(); }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < tend) {
        int k = Ks[rndi(10)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 30 + 3);
        int k2 = K2s[rndi(13)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        K_ = k;
        alloc_state(2 * k * G_);
        int ok = search(tend, 20000, 3000, 6);
        if (ok && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = u;
                    ne[2 * p + 1] = nb[(size_t)l * N_ + u];
                    p++;
                }
            free(bE);
            bE = ne;
            bEc = cnt;
            bestN = N_;
            minN = N_ + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


C_REPAIR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXV 4200
#define MAXD 16
#define MAXW ((MAXV + 63) / 64)
#define MAXE (MAXV * MAXD / 2 + 256)

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bipartite multigraph-free state: edge k joins A-vertex eu[k] and B-vertex ev[k]. */
static int d_, D_, N, M;
static int eu[MAXE], ev[MAXE];
static int adj[MAXV][MAXD];   /* incident edge ids */
static int deg[MAXV];
static int miss[MAXV];

static int sN, sM;
static int seu[MAXE], sev[MAXE];
static int sadj[MAXV][MAXD];
static int sdeg[MAXV];

static u64 bufA[MAXV * MAXW], bufB[MAXV * MAXW];

static int other(int k, int v) { return eu[k] == v ? ev[k] : eu[k]; }

static int has_nb(int v, int w) {
    for (int t = 0; t < deg[v]; t++)
        if (other(adj[v][t], v) == w) return 1;
    return 0;
}

static void repl(int v, int oldk, int newk) {
    for (int t = 0; t < deg[v]; t++)
        if (adj[v][t] == oldk) { adj[v][t] = newk; return; }
}

static void push_e(int v, int k) { adj[v][deg[v]++] = k; }

/* Exchange endpoints: edge i = (a1,b1), j = (a2,b2) become (a1,b2), (a2,b1). Unchecked; self-inverse. */
static void do_swap(int i, int j) {
    int b1 = ev[i], b2 = ev[j];
    repl(b1, i, j);
    repl(b2, j, i);
    ev[i] = b2;
    ev[j] = b1;
}

static int try_swap(int i, int j) {
    if (i == j) return 0;
    int a1 = eu[i], a2 = eu[j], b1 = ev[i], b2 = ev[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_nb(a1, b2) || has_nb(a2, b1)) return 0;
    do_swap(i, j);
    return 1;
}

/* Unreached ordered pairs at distance > D. Also fills miss[v]. */
static long long eval_cost(void) {
    int W = (N + 63) / 64;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] = 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(u64) * W);
            for (int s = 0; s < deg[v]; s++) {
                int u = other(adj[v][s], v);
                const u64 *src = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long unreached = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[(size_t)v * W + w]);
        miss[v] = N - c;
        unreached += N - c;
    }
    return unreached;
}

static void save_state(void) {
    sN = N; sM = M;
    memcpy(seu, eu, sizeof(int) * (size_t)M);
    memcpy(sev, ev, sizeof(int) * (size_t)M);
    memcpy(sadj, adj, sizeof adj);
    memcpy(sdeg, deg, sizeof(int) * (size_t)N);
}

static void restore_state(void) {
    N = sN; M = sM;
    memcpy(eu, seu, sizeof(int) * (size_t)M);
    memcpy(ev, sev, sizeof(int) * (size_t)M);
    memcpy(adj, sadj, sizeof adj);
    memcpy(deg, sdeg, sizeof(int) * (size_t)N);
}

/* Add two vertices a (side A) and b (side B), each of degree d. Each step subdivides
   an existing edge (x,y): it becomes (a,y), and the new edge (x,b) is added. */
static int add_pair(void) {
    if (N + 2 > MAXV) return 0;
    int a = N, b = N + 1;
    N += 2;
    deg[a] = 0; deg[b] = 0;
    long long tries = 0;
    while (deg[a] < d_) {
        if (++tries > 2000000) return 0;
        if (M + 1 > MAXE) return 0;
        int k = rndi(M);
        int x = eu[k], y = ev[k];
        if (has_nb(a, y) || has_nb(b, x)) continue;
        int m2 = M;
        repl(x, k, m2);
        eu[k] = a; ev[k] = y;
        push_e(a, k);
        eu[m2] = x; ev[m2] = b;
        push_e(b, m2);
        M++;
    }
    return 1;
}

/* Simulated annealing with double-edge swaps; half the moves target an edge at a deficient vertex. */
static long long repair(double tend, long long maxit) {
    long long cur = eval_cost();
    double T0 = 15.0;
    for (long long it = 0; it < maxit && cur > 0; it++) {
        if ((it & 31) == 0 && now() > tend) break;
        double frac = (double)it / (double)maxit;
        double T = T0 * (1.0 - frac) + 0.5;
        int i, j;
        if (rndu() < 0.5) {
            int v = -1;
            for (int tries = 0; tries < 32; tries++) {
                int w = rndi(N);
                if (miss[w] > 0) { v = w; break; }
            }
            if (v < 0 || deg[v] == 0) i = rndi(M);
            else i = adj[v][rndi(deg[v])];
        } else {
            i = rndi(M);
        }
        j = rndi(M);
        if (!try_swap(i, j)) continue;
        long long c2 = eval_cost();
        if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            do_swap(i, j);
        }
    }
    return cur;
}

/* Complete bipartite K_{d,d}: always valid for D >= 2. */
static void init_complete(void) {
    int d = d_;
    N = 2 * d;
    M = 0;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            int k = M++;
            eu[k] = a;
            ev[k] = d + b;
            push_e(a, k);
            push_e(d + b, k);
        }
}

/* Read "n m" + edges from stdin. Returns 1 if the graph is simple, bipartite and within degree d. */
static int load_stdin(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > MAXV || m < 1 || m > MAXE) return 0;
    int *U = malloc(sizeof(int) * (size_t)m);
    int *V = malloc(sizeof(int) * (size_t)m);
    int *dg = calloc((size_t)n, sizeof(int));
    int *off = malloc(sizeof(int) * (size_t)(n + 1));
    int *fill = malloc(sizeof(int) * (size_t)n);
    int *nbr = malloc(sizeof(int) * (size_t)(2 * m));
    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    int ok = 1;
    for (int e = 0; e < m && ok; e++) {
        if (scanf("%d %d", &U[e], &V[e]) != 2) { ok = 0; break; }
        if (U[e] < 0 || U[e] >= n || V[e] < 0 || V[e] >= n || U[e] == V[e]) { ok = 0; break; }
        dg[U[e]]++; dg[V[e]]++;
    }
    for (int v = 0; v < n && ok; v++) if (dg[v] > d_) ok = 0;
    if (ok) {
        off[0] = 0;
        for (int v = 0; v < n; v++) { off[v + 1] = off[v] + dg[v]; fill[v] = off[v]; }
        for (int e = 0; e < m; e++) {
            nbr[fill[U[e]]++] = V[e];
            nbr[fill[V[e]]++] = U[e];
        }
        /* duplicate check */
        for (int v = 0; v < n && ok; v++)
            for (int t = off[v]; t < off[v + 1] && ok; t++)
                for (int s = t + 1; s < off[v + 1]; s++)
                    if (nbr[t] == nbr[s]) { ok = 0; break; }
    }
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt && ok) {
                int u = q[qh++];
                for (int t = off[u]; t < off[u + 1]; t++) {
                    int w = nbr[t];
                    if (col[w] == -1) { col[w] = 1 - col[u]; q[qt++] = w; }
                    else if (col[w] == col[u]) { ok = 0; break; }
                }
            }
        }
    }
    if (ok) {
        N = n; M = m;
        for (int v = 0; v < n; v++) deg[v] = 0;
        for (int e = 0; e < m; e++) {
            int a = U[e], b = V[e];
            if (col[a]) { int t = a; a = b; b = t; }
            eu[e] = a; ev[e] = b;
            push_e(a, e);
            push_e(b, e);
        }
    }
    free(U); free(V); free(dg); free(off); free(fill); free(nbr); free(col); free(q);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    if (!load_stdin() || eval_cost() != 0) init_complete();
    if (eval_cost() != 0) { printf("0 0\n"); return 0; }
    save_state();

    long long maxit = 6000;
    int fails = 0;
    while (now() < tend) {
        long long c = repair(tend, maxit);
        if (c == 0) {
            save_state();
            fails = 0;
            maxit = 6000;
        } else {
            restore_state();
            fails++;
            if (fails % 3 == 0 && maxit < 200000) maxit *= 2;
        }
        if (now() >= tend) break;
        if (!add_pair()) { restore_state(); break; }
    }

    printf("%d %d\n", sN, sM);
    for (int e = 0; e < sM; e++) printf("%d %d\n", seu[e], sev[e]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    # Budget: about 7 s is reserved for compiling the two C programs and Python glue.
    budget = time_limit - 7.0
    if budget < 2.0:
        return best

    # Phase 1: group-lift search (the parent's engine) gives a valid structured graph.
    # Phase 2: unstructured add-pair and annealing repair starts from that graph.
    lift_budget = 0.6 * budget
    rep_budget = budget - lift_budget

    try:
        out = lib.run_c(C_LIFT, [d, D, seed, round(lift_budget, 2), best_n + 1],
                        timeout=lift_budget + 2.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    try:
        out = lib.run_c(C_REPAIR, [d, D, seed, round(rep_budget, 2)],
                        stdin_graph=best, timeout=rep_budget + 2.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

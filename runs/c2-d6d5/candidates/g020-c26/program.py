import lib


C_SOURCE = r'''
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
#define MAXNV 2000

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

/* ===================== Part 1: group voltage-lift search ===================== */

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

/* Simulated annealing with iterated-local-search kicks from the best state.
   Returns 1 when a valid graph (cost 0) is in the current state. */
static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_;
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
                int start = rndi(N_), v = -1;
                for (int q = 0; q < N_; q++) {
                    int w = (start + q) % N_;
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

static void lift_search(double tl, int minN) {
    double tend = now() + tl;
    double slice = tl / 6.0;
    if (slice < 1.0) slice = 1.0;
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
        double gend = now() + slice;
        if (gend > tend) gend = tend;
        int ok = search(gend, 20000, 3000, 6);
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
}

/* ===================== Part 2: general-graph repair ===================== */
/* Grow a d-regular bipartite graph by one A-vertex and one B-vertex:
   take d disjoint edges (a_k, b_k), then rewire a_k-y and x-b_k.
   Degrees stay d. Then anneal with degree-preserving 2-switches
   that minimise the number of ordered vertex pairs at distance > D. */

static int *gA = NULL;   /* current valid graph: adjacency rows, gN * d_ */
static int *gS = NULL;   /* side per vertex: 0 = A, 1 = B */
static int gN = 0;

static int rep_has(const int *row, int d, int x) {
    for (int l = 0; l < d; l++) if (row[l] == x) return 1;
    return 0;
}

static int rep_find(const int *row, int d, int x) {
    for (int l = 0; l < d; l++) if (row[l] == x) return l;
    return -1;
}

/* Bitset BFS. Returns sum over v of unreached vertices. Final reach sets land in out;
   cnt[v] = number of vertices unreached from v. */
static long long reach_eval(int NV, int d, int Dd, const int *adj, u64 *out, u64 *scr, int *cnt) {
    int W = (NV + 63) >> 6;
    u64 *cur = out, *nx = scr;
    memset(cur, 0, sizeof(u64) * (size_t)NV * W);
    for (int v = 0; v < NV; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < Dd; t++) {
        for (int v = 0; v < NV; v++) {
            u64 *dst = nx + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int l = 0; l < d; l++) {
                const u64 *s2 = cur + (size_t)adj[v * d + l] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *sw = cur; cur = nx; nx = sw;
    }
    long long cost = 0;
    for (int v = 0; v < NV; v++) {
        int c = 0;
        const u64 *r = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(r[w]);
        cnt[v] = NV - c;
        cost += NV - c;
    }
    if (cur != out) memcpy(out, cur, sizeof(u64) * (size_t)NV * W);
    return cost;
}

/* adj has room for NV+2 rows; rows 0..NV-1 hold the base graph. Adds x = NV (side A)
   and y = NV+1 (side B). Returns 0 if d disjoint edges could not be chosen. */
static int rep_insert(int NV, int d, int *adj, int *side) {
    int x = NV, y = NV + 1;
    side[x] = 0; side[y] = 1;
    int *Al = malloc(sizeof(int) * (size_t)(NV + 1));
    int nA = 0;
    for (int v = 0; v < NV; v++) if (side[v] == 0) Al[nA++] = v;
    for (int i = nA - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = Al[i]; Al[i] = Al[j]; Al[j] = t;
    }
    int pa[MAXD], ps[MAXD], pb[MAXD];
    int got = 0;
    for (int q = 0; q < nA && got < d; q++) {
        int a = Al[q];
        int s = rndi(d);
        int b = adj[a * d + s];
        int used = 0;
        for (int k = 0; k < got; k++) if (pb[k] == b) { used = 1; break; }
        if (used) continue;
        pa[got] = a; ps[got] = s; pb[got] = b; got++;
    }
    free(Al);
    if (got < d) return 0;
    for (int k = 0; k < d; k++) {
        int a = pa[k], s = ps[k], b = pb[k];
        int t = rep_find(adj + b * d, d, a);
        if (t < 0) return 0;
        adj[a * d + s] = y;
        adj[b * d + t] = x;
        adj[x * d + k] = b;
        adj[y * d + k] = a;
    }
    return 1;
}

/* Anneal on a graph with NN vertices. Returns 1 if the graph reaches diameter Dd. */
static int rep_anneal(int NN, int d, int Dd, int *adj, const int *side, int iters, double tend) {
    int W = (NN + 63) >> 6;
    size_t sz = (size_t)NN * W;
    u64 *bC = malloc(sizeof(u64) * sz);
    u64 *bN = malloc(sizeof(u64) * sz);
    u64 *bS = malloc(sizeof(u64) * sz);
    int *cC = malloc(sizeof(int) * (size_t)NN);
    int *cN = malloc(sizeof(int) * (size_t)NN);
    int *Al = malloc(sizeof(int) * (size_t)NN);
    int nA = 0;
    for (int v = 0; v < NN; v++) if (side[v] == 0) Al[nA++] = v;

    long long cur = reach_eval(NN, d, Dd, adj, bC, bS, cC);
    int ok = (cur == 0);
    double T0 = 1.5 + 0.02 * (double)cur;

    for (int t = 0; !ok && t < iters; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        double T = T0 * (1.0 - (double)t / iters);
        if (T < 0.15) T = 0.15;

        int a, i, c, j;
        if (rndu() < 0.5) {
            /* Defect-targeted: pick an unhappy vertex and switch one of its edges. */
            int st = rndi(NN), v = -1;
            for (int q = 0; q < NN; q++) {
                int w = (st + q) % NN;
                if (cC[w] > 0) { v = w; break; }
            }
            if (v < 0) continue;
            if (side[v] == 0) {
                a = v;
                i = rndi(d);
            } else {
                int s = rndi(d);
                a = adj[v * d + s];
                i = rep_find(adj + a * d, d, v);
                if (i < 0) continue;
            }
        } else {
            a = Al[rndi(nA)];
            i = rndi(d);
        }
        c = Al[rndi(nA)];
        j = rndi(d);
        if (c == a) continue;

        int b = adj[a * d + i], e = adj[c * d + j];
        if (b == e) continue;
        if (rep_has(adj + a * d, d, e) || rep_has(adj + c * d, d, b)) continue;
        int p = rep_find(adj + e * d, d, c);
        int q2 = rep_find(adj + b * d, d, a);
        if (p < 0 || q2 < 0) continue;

        /* 2-switch: (a,b),(c,e) -> (a,e),(c,b). */
        adj[a * d + i] = e;
        adj[c * d + j] = b;
        adj[e * d + p] = a;
        adj[b * d + q2] = c;

        long long nc = reach_eval(NN, d, Dd, adj, bN, bS, cN);
        long long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
            u64 *tb = bC; bC = bN; bN = tb;
            int *tc = cC; cC = cN; cN = tc;
            if (cur == 0) ok = 1;
        } else {
            adj[a * d + i] = b;
            adj[c * d + j] = e;
            adj[e * d + p] = c;
            adj[b * d + q2] = a;
        }
    }
    free(bC); free(bN); free(bS);
    free(cC); free(cN); free(Al);
    return ok;
}

static void repair_search(double tl, int d, int Dd) {
    double tend = now() + tl;
    int iters = 12000;
    while (now() < tend && gN + 2 <= MAXNV) {
        int NV = gN, NN = gN + 2;
        int *adj = malloc(sizeof(int) * (size_t)NN * d);
        int *side = malloc(sizeof(int) * (size_t)NN);
        memcpy(adj, gA, sizeof(int) * (size_t)NV * d);
        memcpy(side, gS, sizeof(int) * (size_t)NV);
        if (!rep_insert(NV, d, adj, side)) { free(adj); free(side); continue; }
        if (rep_anneal(NN, d, Dd, adj, side, iters, tend)) {
            free(gA); free(gS);
            gA = adj; gS = side; gN = NN;
        } else {
            free(adj); free(side);
        }
    }
}

/* Read a d-regular bipartite graph into gA / gS. Returns 0 if it does not fit. */
static int load_input(int n, int m, const int *eu, const int *ev, int d) {
    int *deg = calloc((size_t)n, sizeof(int));
    for (int p = 0; p < m; p++) {
        int u = eu[p], v = ev[p];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { free(deg); return 0; }
        deg[u]++; deg[v]++;
    }
    for (int v = 0; v < n; v++) if (deg[v] != d) { free(deg); return 0; }
    int *adj = malloc(sizeof(int) * (size_t)n * d);
    int *fill = calloc((size_t)n, sizeof(int));
    for (int p = 0; p < m; p++) {
        int u = eu[p], v = ev[p];
        adj[u * d + fill[u]++] = v;
        adj[v * d + fill[v]++] = u;
    }
    free(fill);
    int *side = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) side[v] = -1;
    int *queue = malloc(sizeof(int) * (size_t)n);
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int u = queue[qh++];
            for (int l = 0; l < d; l++) {
                int w = adj[u * d + l];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                } else if (side[w] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    free(queue);
    free(deg);
    if (!ok) { free(adj); free(side); return 0; }
    free(gA); free(gS);
    gA = adj; gS = side; gN = n;
    return 1;
}

static void print_state(int d) {
    int m = 0;
    for (int v = 0; v < gN; v++) if (gS[v] == 0) m += d;
    printf("%d %d\n", gN, m);
    for (int v = 0; v < gN; v++)
        if (gS[v] == 0)
            for (int l = 0; l < d; l++) printf("%d %d\n", v, gA[v * d + l]);
}

/* ===================== main ===================== */

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

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }

    if (sn > 0 && sm > 0) {
        /* Repair mode: start graph given on stdin. */
        int *eu = malloc(sizeof(int) * (size_t)sm);
        int *ev = malloc(sizeof(int) * (size_t)sm);
        int ok = 1;
        for (int p = 0; p < sm; p++) {
            if (scanf("%d %d", &eu[p], &ev[p]) != 2) { ok = 0; break; }
        }
        if (ok && load_input(sn, sm, eu, ev, d_)) {
            repair_search(tl, d_, D_);
            print_state(d_);
        } else {
            printf("0 0\n");
        }
        free(eu); free(ev);
        return 0;
    }

    /* Lift mode: group voltage-lift search. */
    lift_search(tl, minN);
    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))

    # Stage 1: group voltage-lift search for a large regular bipartite graph.
    lift_t = 0.4 * budget
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(lift_t, 2), best_n + 1],
                        timeout=lift_t + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: grow the best regular graph by vertex pairs and anneal each step.
    rep_t = budget - lift_t - 1.0
    if rep_t >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed + 1, round(rep_t, 2), 2],
                            stdin_graph=best, timeout=rep_t + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

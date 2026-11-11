import time

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

/* Simulated annealing with iterated-local-search kicks from the best state.
   Returns 1 when a valid graph (cost 0) is in the current state. */
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
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
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
            /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
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


# Phase 2: general bipartite graph, simulated annealing with degree-preserving
# moves and vertex growth. Input: bipartite graph with A = 0..N-1, B = N..2N-1.
C_SOURCE2 = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
#define CAP 1024
#define WMAX ((2 * CAP + 63) / 64)

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

static int d_, D_, N_;
static int adjA[CAP * 16], adjB[CAP * 16];
static int degA[CAP], degB[CAP];
static unsigned char M[CAP * CAP];
static u64 *R1, *R2;
static int bestN = 0, bestCnt = 0;
static int bestEA[CAP * 16], bestEB[CAP * 16];

typedef struct { int t, a, b; } Op;
static Op ops[8];
static int nops = 0;

static void arr_remove(int *arr, int *dg, int val) {
    for (int i = 0; i < *dg; i++)
        if (arr[i] == val) { arr[i] = arr[*dg - 1]; (*dg)--; return; }
}
static void addE(int a, int b) {
    adjA[a * d_ + degA[a]++] = b;
    adjB[b * d_ + degB[b]++] = a;
    M[a * CAP + b] = 1;
}
static void remE(int a, int b) {
    arr_remove(adjA + a * d_, &degA[a], b);
    arr_remove(adjB + b * d_, &degB[b], a);
    M[a * CAP + b] = 0;
}
static void doadd(int a, int b) { addE(a, b); ops[nops++] = (Op){1, a, b}; }
static void dorem(int a, int b) { remE(a, b); ops[nops++] = (Op){-1, a, b}; }
static void undo(void) {
    while (nops > 0) {
        Op o = ops[--nops];
        if (o.t == 1) remE(o.a, o.b);
        else addE(o.a, o.b);
    }
}

/* Unreached ordered pairs within distance D_ (0 means valid). */
static long long evalc(void) {
    int N = N_, V = 2 * N, W = (V + 63) / 64, d = d_;
    memset(R1, 0, sizeof(u64) * (size_t)V * W);
    for (int r = 0; r < V; r++) R1[(size_t)r * W + (r >> 6)] |= 1ULL << (r & 63);
    for (int t = 0; t < D_; t++) {
        for (int r = 0; r < V; r++) {
            u64 *out = R2 + (size_t)r * W;
            const u64 *in = R1 + (size_t)r * W;
            for (int w = 0; w < W; w++) out[w] = in[w];
            if (r < N) {
                for (int k = 0; k < degA[r]; k++) {
                    const u64 *x = R1 + (size_t)(N + adjA[r * d + k]) * W;
                    for (int w = 0; w < W; w++) out[w] |= x[w];
                }
            } else {
                int j = r - N;
                for (int k = 0; k < degB[j]; k++) {
                    const u64 *x = R1 + (size_t)adjB[j * d + k] * W;
                    for (int w = 0; w < W; w++) out[w] |= x[w];
                }
            }
        }
        u64 *s = R1; R1 = R2; R2 = s;
    }
    long long cnt = 0;
    for (int r = 0; r < V; r++)
        for (int w = 0; w < W; w++) cnt += popc(R1[(size_t)r * W + w]);
    return (long long)V * V - cnt;
}

static void save_best(void) {
    int n = 0;
    for (int a = 0; a < N_; a++)
        for (int k = 0; k < degA[a]; k++) {
            bestEA[n] = a;
            bestEB[n] = adjA[a * d_ + k];
            n++;
        }
    bestCnt = n;
    bestN = N_;
}

/* One degree-preserving or deficit-filling move. Returns 0 if no move was made. */
static int move(void) {
    int N = N_, d = d_, V = 2 * N;
    nops = 0;
    int start = rndi(V), r = -1;
    for (int q = 0; q < V; q++) {
        int w = (start + q) % V;
        int dg = (w < N) ? degA[w] : degB[w - N];
        if (dg < d) { r = w; break; }
    }
    if (r >= 0) {
        if (r < N) {
            int x = r, b = rndi(N);
            if (M[x * CAP + b]) return 0;
            if (degB[b] < d) doadd(x, b);
            else {
                int a = adjB[b * d + rndi(d)];
                dorem(a, b);
                doadd(x, b);
            }
        } else {
            int y = r - N, a = rndi(N);
            if (M[a * CAP + y]) return 0;
            if (degA[a] < d) doadd(a, y);
            else {
                int b = adjA[a * d + rndi(d)];
                dorem(a, b);
                doadd(a, y);
            }
        }
        return 1;
    }
    /* All degrees are d: double edge switch. */
    int a = rndi(N), c = rndi(N);
    if (a == c) return 0;
    int b = adjA[a * d + rndi(d)];
    int e = adjA[c * d + rndi(d)];
    if (M[a * CAP + e] || M[c * CAP + b]) return 0;
    dorem(a, b);
    dorem(c, e);
    doadd(a, e);
    doadd(c, b);
    return 1;
}

static long long grow(void) {
    N_++;
    degA[N_ - 1] = 0;
    degB[N_ - 1] = 0;
    return evalc();
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 2 || d_ > 16 || D_ < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    R1 = malloc(sizeof(u64) * 2 * CAP * WMAX);
    R2 = malloc(sizeof(u64) * 2 * CAP * WMAX);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int N0 = n / 2;
    if (N0 > CAP - 4) N0 = CAP - 4;
    N_ = N0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || u >= N0 || v < N0 || v >= 2 * N0) continue;
        int a = u, b = v - N0;
        if (degA[a] >= d_ || degB[b] >= d_ || M[a * CAP + b]) continue;
        addE(a, b);
    }
    if (N_ < 1) N_ = d_;

    double tend = now() + tl;
    long long cur = evalc();
    if (cur == 0) save_best();

    const long long EPOCH = 40000;
    const double Tmax = 8.0, Tmin = 0.4;
    long long it = 0;
    while (1) {
        if ((it & 63) == 0 && now() > tend) break;
        double frac = (double)(it % EPOCH) / (double)EPOCH;
        double T = Tmax * pow(Tmin / Tmax, frac);
        it++;
        if (!move()) continue;
        long long c2 = evalc();
        long long delta = c2 - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) {
                if (N_ > bestN) save_best();
                if (N_ < CAP - 2) cur = grow();
            }
        } else {
            undo();
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestN, bestCnt);
    for (int p = 0; p < bestCnt; p++)
        printf("%d %d\n", bestEA[p], bestN + bestEB[p]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, edges):
    """Return a 0/1 colour per vertex, or None if the graph is not bipartite."""
    adj = lib.adjacency(n, edges)
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


def _relabel_bip(n, edges):
    """Return (N, edges') with A = 0..N-1 and B = N..2N-1 (padded to equal sides), or None."""
    col = _bipartition(n, edges)
    if col is None:
        return None
    A = [v for v in range(n) if col[v] == 0]
    B = [v for v in range(n) if col[v] == 1]
    N = max(len(A), len(B))
    if N < 1:
        return None
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: i for i, v in enumerate(B)}
    out = []
    for u, v in edges:
        if col[u] == 1:
            u, v = v, u
        out.append((ia[u], N + ib[v]))
    return N, out


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

    total = max(2.0, time_limit - 10.0)

    # Phase 1: group-lift search (the parent engine) for a strong start graph.
    budget1 = total * 0.6
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget1, 2), best_n + 1],
                        timeout=budget1 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: grow the best graph by annealing on general bipartite graphs.
    budget2 = total - budget1
    try:
        rel = _relabel_bip(best[0], best[1])
        if rel is not None:
            N, g = rel
            out = lib.run_c(C_SOURCE2, [d, D, seed + 1, round(budget2, 2)],
                            stdin_graph=(2 * N, g), timeout=budget2 + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

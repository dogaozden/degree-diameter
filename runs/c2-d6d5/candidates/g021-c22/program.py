import lib


C_GROW = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXV 1400
#define MAXW ((MAXV + 63) / 64)
#define MAXDEG 16
#define PATIENCE 20000

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

/* Growth-based search over general (non-group) bipartite graphs with max degree d.
   State: vertices 0..nv-1, even-indexed-by-creation pairs (A, B), edges only A-B.
   Cost = number of ordered vertex pairs at distance > D. Moves: add edge, degree-
   preserving switch, remove edge; Metropolis acceptance. When cost hits 0 the graph
   is recorded and two new vertices (one per side) are appended. */

static int D_, d_, nv = 0, nA = 0, nB = 0;
static int deg[MAXV], adj[MAXV][MAXDEG];
static int LA[MAXV], LB[MAXV], candA[MAXV], candB[MAXV];
static u64 RA[MAXV * MAXW], RB[MAXV * MAXW];
static int bdeg[MAXV], badj[MAXV][MAXDEG], bnv = 0;
static int OE[MAXV * MAXDEG * 2], outN = 0, outM = 0;

static long long evalbad(void) {
    int N = nv, W = (N + 63) / 64;
    u64 *P = RA, *Q = RB;
    memset(P, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) P[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = Q + (size_t)v * W;
            const u64 *c = P + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int j = 0; j < deg[v]; j++) {
                const u64 *c2 = P + (size_t)adj[v][j] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        u64 *sw = P; P = Q; Q = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(P[i]);
    return (long long)N * N - cnt;
}

static int has_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) return 1;
    return 0;
}

static void del_half(int a, int b) {
    for (int j = 0; j < deg[a]; j++)
        if (adj[a][j] == b) { adj[a][j] = adj[a][--deg[a]]; return; }
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static int rand_edge(int *pa, int *pb) {
    for (int tries = 0; tries < 100; tries++) {
        int a = LA[rndi(nA)];
        if (deg[a] == 0) continue;
        *pa = a;
        *pb = adj[a][rndi(deg[a])];
        return 1;
    }
    return 0;
}

static int grow(void) {
    if (nv + 2 > MAXV) return 0;
    int a = nv, b = nv + 1;
    deg[a] = deg[b] = 0;
    LA[nA++] = a;
    LB[nB++] = b;
    nv += 2;
    return 1;
}

static void snap(void) {
    memcpy(bdeg, deg, sizeof(int) * (size_t)nv);
    memcpy(badj, adj, sizeof(adj[0]) * (size_t)nv);
    bnv = nv;
}

static void restore(void) {
    memcpy(deg, bdeg, sizeof(int) * (size_t)bnv);
    memcpy(adj, badj, sizeof(adj[0]) * (size_t)bnv);
}

static void record(void) {
    int m = 0;
    for (int u = 0; u < nv; u++)
        for (int j = 0; j < deg[u]; j++) {
            int v = adj[u][j];
            if (u < v) { OE[2 * m] = u; OE[2 * m + 1] = v; m++; }
        }
    outN = nv;
    outM = m;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int s0 = argc > 5 ? atoi(argv[5]) : 3;
    if (d_ < 3 || D_ < 3 || d_ > MAXDEG) { printf("0 0\n"); return 0; }
    if (s0 < 1) s0 = 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    for (int i = 0; i < s0; i++) grow();
    long long cur = evalbad();
    long long bestc = cur;
    snap();
    int since = 0;

    while (now() < tend) {
        if (cur == 0) {
            record();
            if (!grow()) break;
            cur = evalbad();
            bestc = cur;
            since = 0;
            snap();
            continue;
        }
        since++;
        if (since > PATIENCE) {
            restore();
            int rem = 1 + rndi(3);
            for (int q = 0; q < rem; q++) {
                int a, b;
                if (rand_edge(&a, &b)) del_edge(a, b);
            }
            cur = evalbad();
            since = 0;
            continue;
        }

        double T = 0.004 * (double)cur;
        if (T < 0.5) T = 0.5;
        double u = rndu();

        if (u < 0.40) {
            /* Add an edge between a deficient A and a deficient B vertex. */
            int ca = 0, cb = 0;
            for (int i = 0; i < nA; i++) if (deg[LA[i]] < d_) candA[ca++] = LA[i];
            for (int i = 0; i < nB; i++) if (deg[LB[i]] < d_) candB[cb++] = LB[i];
            if (ca == 0 || cb == 0) continue;
            int a = -1, b = -1;
            for (int tr = 0; tr < 10; tr++) {
                int x = candA[rndi(ca)], y = candB[rndi(cb)];
                if (!has_edge(x, y)) { a = x; b = y; break; }
            }
            if (a < 0) continue;
            add_edge(a, b);
            long long nc = evalbad();
            if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) cur = nc;
            else del_edge(a, b);
        } else if (u < 0.95) {
            /* Degree-preserving switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
            int a1, b1, a2, b2;
            if (!rand_edge(&a1, &b1) || !rand_edge(&a2, &b2)) continue;
            if (a1 == a2 || b1 == b2) continue;
            if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
            del_edge(a1, b1);
            del_edge(a2, b2);
            add_edge(a1, b2);
            add_edge(a2, b1);
            long long nc = evalbad();
            if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) cur = nc;
            else {
                del_edge(a1, b2);
                del_edge(a2, b1);
                add_edge(a1, b1);
                add_edge(a2, b2);
            }
        } else {
            /* Remove a random edge (lets degrees be re-spent elsewhere). */
            int a, b;
            if (!rand_edge(&a, &b)) continue;
            del_edge(a, b);
            long long nc = evalbad();
            if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) cur = nc;
            else add_edge(a, b);
        }
        if (cur < bestc) { bestc = cur; since = 0; snap(); }
    }

    if (cur == 0) record();
    if (outN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", outN, outM);
    for (int p = 0; p < outM; p++) printf("%d %d\n", OE[2 * p], OE[2 * p + 1]);
    return 0;
}
'''


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

    # Two engines share the budget: the new unstructured growth search,
    # then the group-lift search as a safety net so the score cannot collapse.
    total = max(0.5, min(0.8 * time_limit, time_limit - 10.0))
    half = total / 2.0

    try:
        out = lib.run_c(C_GROW, [d, D, seed, round(half, 2), 3],
                        timeout=half + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    try:
        out = lib.run_c(C_LIFT, [d, D, seed, round(half, 2), best_n + 1],
                        timeout=half + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

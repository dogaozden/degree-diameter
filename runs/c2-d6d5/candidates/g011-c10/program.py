import lib


PARENT_C = r'''
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


GROW_C = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define CAP 2048

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

/* Current graph: bipartite, degrees <= d_. Edge e = (E[e][0] in side A, E[e][1] in side B). */
static int d_, D_, N_, M_;
static int deg[CAP];
static int nb[CAP * MAXD];
static int E[CAP * MAXD][2];
static u64 RA[CAP * (CAP / 64)], RB[CAP * (CAP / 64)];

/* Saved valid graph. */
static int sN, sM;
static int sdeg[CAP];
static int snb[CAP * MAXD];
static int sE[CAP * MAXD][2];

static void save(void) {
    sN = N_; sM = M_;
    memcpy(sdeg, deg, sizeof deg);
    memcpy(snb, nb, sizeof nb);
    memcpy(sE, E, sizeof E);
}

static void restore(void) {
    N_ = sN; M_ = sM;
    memcpy(deg, sdeg, sizeof deg);
    memcpy(nb, snb, sizeof nb);
    memcpy(E, sE, sizeof E);
}

static int adj(int u, int v) {
    for (int j = 0; j < deg[u]; j++) if (nb[u * MAXD + j] == v) return 1;
    return 0;
}

static void repl(int u, int old, int nw) {
    for (int j = 0; j < deg[u]; j++)
        if (nb[u * MAXD + j] == old) { nb[u * MAXD + j] = nw; return; }
}

static void addnb(int u, int v) {
    nb[u * MAXD + deg[u]] = v;
    deg[u]++;
}

/* Degree-preserving 2-switch: (p,q),(r,s) -> (p,s),(r,q). Applying it twice reverts. */
static void do_switch(int e1, int e2) {
    int p = E[e1][0], q = E[e1][1], r = E[e2][0], s = E[e2][1];
    repl(p, q, s);
    repl(q, p, r);
    repl(r, s, q);
    repl(s, r, p);
    E[e1][0] = p; E[e1][1] = s;
    E[e2][0] = r; E[e2][1] = q;
}

/* Cost = number of unordered pairs at distance > D_ (unreached pairs). */
static long long evalcost(void) {
    int N = N_, W = (N + 63) >> 6, d = d_;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int j = 0; j < deg[v]; j++) {
                const u64 *c2 = cur + (size_t)nb[v * MAXD + j] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    (void)d;
    long long cnt = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) cnt += popc(cur[(size_t)v * W + w]);
    long long bad = (long long)N * N - cnt;
    return bad / 2;
}

/* Insert two new vertices a (side A) and b (side B). Each takes d_ edges by subdividing
   existing edges (x,y) -> (a,y) and (x,b); existing degrees are preserved. */
static int add_pair(void) {
    int d = d_;
    if (N_ + 2 > CAP) return 0;
    int a = N_, b = N_ + 1;
    N_ += 2;
    deg[a] = 0; deg[b] = 0;
    int added = 0;
    long long tries = 0;
    while (added < d && tries < 200000) {
        tries++;
        int e = rndi(M_);
        int x = E[e][0], y = E[e][1];
        if (adj(a, y) || adj(b, x)) continue;
        repl(x, y, b);
        repl(y, x, a);
        addnb(a, y);
        addnb(b, x);
        E[e][0] = a; E[e][1] = y;
        if (M_ >= CAP * MAXD) return 0;
        E[M_][0] = x; E[M_][1] = b;
        M_++;
        added++;
    }
    return added == d;
}

static int anneal(double tend, long long maxit) {
    long long cost = evalcost();
    if (cost == 0) return 1;
    double T0 = 0.5 + 0.05 * (double)cost;
    for (long long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 15) == 0 && now() > tend) break;
        int e1 = rndi(M_), e2 = rndi(M_);
        if (e1 == e2) continue;
        int p = E[e1][0], q = E[e1][1], r = E[e2][0], s = E[e2][1];
        if (p == r || q == s) continue;
        if (adj(p, s) || adj(r, q)) continue;
        do_switch(e1, e2);
        long long c2 = evalcost();
        long long delta = c2 - cost;
        double T = T0 * (1.0 - (double)it / (double)maxit) + 0.1;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            do_switch(e1, e2);
        }
    }
    return cost == 0;
}

static int readgraph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > CAP || m < 0 || m > CAP * MAXD / 2) return 0;
    static int U[CAP * MAXD / 2], V[CAP * MAXD / 2];
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d_ || deg[v] >= d_) return 0;
        if (adj(u, v)) return 0;
        addnb(u, v);
        addnb(v, u);
        U[i] = u; V[i] = v;
    }
    static int colr[CAP], q[CAP];
    for (int v = 0; v < n; v++) colr[v] = -1;
    for (int s = 0; s < n; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++];
            for (int j = 0; j < deg[x]; j++) {
                int y = nb[x * MAXD + j];
                if (colr[y] < 0) { colr[y] = 1 - colr[x]; q[tail++] = y; }
                else if (colr[y] == colr[x]) return 0;
            }
        }
    }
    for (int i = 0; i < m; i++) {
        if (colr[U[i]] == 0) { E[i][0] = U[i]; E[i][1] = V[i]; }
        else { E[i][0] = V[i]; E[i][1] = U[i]; }
    }
    N_ = n;
    M_ = m;
    return 1;
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
    if (!readgraph()) { printf("0 0\n"); return 0; }
    if (evalcost() != 0) { printf("0 0\n"); return 0; }
    save();

    while (now() < tend) {
        restore();
        if (!add_pair()) continue;
        if (anneal(tend, 20000)) save();
    }

    printf("%d %d\n", sN, sM);
    for (int e = 0; e < sM; e++) printf("%d %d\n", sE[e][0], sE[e][1]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record-type graph for degree d when d-2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if d < 3 or D < 3:
        return best

    # Stage 1: group-lift search (parent engine) for most of the budget.
    # Stage 2: a different engine that grows the best graph by inserting vertex
    # pairs and repairing diameter with degree-preserving 2-switch annealing.
    total = max(0.5, time_limit - 8.0)
    t1 = total * 0.7
    t2 = total - t1

    try:
        out = lib.run_c(PARENT_C, [d, D, seed, round(t1, 2), best_n + 1],
                        timeout=t1 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if t2 >= 1.0:
        try:
            out = lib.run_c(GROW_C, [d, D, seed + 7, round(t2, 2)],
                            stdin_graph=best, timeout=t2 + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

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

/* ---------- Phase 1: group-lift search (voltage lifts over Z_m x| Z_k2) ---------- */

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
    int k = K_, d = d_, G = G_;
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
                    if (rch[w] != ((1ULL << (2 * k)) - 1)) { v = w; break; }
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

static void group_phase(double tend, int minN) {
    static int cand[GMAX + 5];
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
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
}

/* ---------- Phase 2: grow a valid regular bipartite graph by adding vertex pairs,
   then repair with edge-switch simulated annealing on the bad-pair count. ---------- */

static int *an_nb = NULL;          /* working graph: A = 0..h-1, B = h..2h-1, d-regular */
static u64 *an_cur = NULL, *an_nxt = NULL;
static int *vnb = NULL;            /* last fully valid graph */
static int vh = 0;

static void an_alloc(int N) {
    int W = (N + 63) / 64;
    free(an_cur); free(an_nxt);
    an_cur = malloc(sizeof(u64) * (size_t)N * W);
    an_nxt = malloc(sizeof(u64) * (size_t)N * W);
}

/* Number of unordered vertex pairs at distance > D_ (0 iff valid). */
static long long an_eval(int h) {
    int d = d_, N = 2 * h, W = (N + 63) / 64;
    u64 *cur = an_cur, *nxt = an_nxt;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(u64) * (size_t)W);
            for (int j = 0; j < d; j++) {
                const u64 *s = cur + (size_t)an_nb[v * d + j] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(cur[i]);
    return ((long long)N * N - cnt) / 2;
}

static int an_adj(int x, int y) {
    int d = d_;
    for (int j = 0; j < d; j++) if (an_nb[x * d + j] == y) return 1;
    return 0;
}

static int an_slot(int x, int y) {
    int d = d_;
    for (int j = 0; j < d; j++) if (an_nb[x * d + j] == y) return j;
    return -1;
}

/* Edge-switch annealing on an_nb (size 2h). Returns cost; 0 means valid and left in an_nb. */
static long long anneal_graph(int h, double tend) {
    int d = d_;
    an_alloc(2 * h);
    long long cost = an_eval(h);
    if (cost == 0) return 0;
    double t0 = now();
    double span = tend - t0;
    if (span <= 0) return cost;
    const double T0 = 4.0, T1 = 0.1;
    double T = T0;
    long long cur = cost;
    for (long long it = 0;; it++) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= tend) break;
            double f = (tn - t0) / span;
            T = T0 * pow(T1 / T0, f);
        }
        int a1 = rndi(h), i1 = rndi(d), a2 = rndi(h), i2 = rndi(d);
        int b1 = an_nb[a1 * d + i1], b2 = an_nb[a2 * d + i2];
        if (a1 == a2 || b1 == b2) continue;
        if (an_adj(a1, b2) || an_adj(a2, b1)) continue;
        int s1 = an_slot(b1, a1), s2 = an_slot(b2, a2);
        an_nb[a1 * d + i1] = b2;
        an_nb[a2 * d + i2] = b1;
        an_nb[b1 * d + s1] = a2;
        an_nb[b2 * d + s2] = a1;
        long long c2 = an_eval(h);
        if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            if (cur == 0) break;
        } else {
            an_nb[a1 * d + i1] = b1;
            an_nb[a2 * d + i2] = b2;
            an_nb[b1 * d + s1] = a1;
            an_nb[b2 * d + s2] = a2;
        }
    }
    return cur;
}

static int addedge(int *g, int *deg, int d, int u, int v) {
    if (u == v || deg[u] >= d || deg[v] >= d) return 0;
    for (int j = 0; j < deg[u]; j++) if (g[u * d + j] == v) return 0;
    g[u * d + deg[u]++] = v;
    g[v * d + deg[v]++] = u;
    return 1;
}

/* Add one A vertex and one B vertex: remove d edges with distinct endpoints
   (a_i, b_i); new A* ~ all b_i, new B* ~ all a_i. Degrees stay d. */
static int *an_expand(const int *src, int h) {
    int d = d_, E = h * d, H = h + 1, NN = 2 * H;
    int *ea = malloc(sizeof(int) * (size_t)E), *eb = malloc(sizeof(int) * (size_t)E);
    char *rem = calloc((size_t)E, 1), *uA = calloc((size_t)h, 1), *uB = calloc((size_t)h, 1);
    int *nn = malloc(sizeof(int) * (size_t)NN * d);
    int *deg = calloc((size_t)NN, sizeof(int));
    int ra[MAXD], rb[MAXD], got = 0, p = 0, ok = 1;
    for (int a = 0; a < h; a++)
        for (int j = 0; j < d; j++) {
            ea[p] = a;
            eb[p] = src[a * d + j] - h;
            p++;
        }
    for (int tries = 0; got < d && tries < 100000; tries++) {
        int e = rndi(E);
        if (rem[e] || uA[ea[e]] || uB[eb[e]]) continue;
        rem[e] = 1; uA[ea[e]] = 1; uB[eb[e]] = 1;
        ra[got] = ea[e]; rb[got] = eb[e]; got++;
    }
    if (got < d) ok = 0;
    for (int e = 0; e < E && ok; e++)
        if (!rem[e]) ok = addedge(nn, deg, d, ea[e], H + eb[e]);
    for (int i = 0; i < d && ok; i++) ok = addedge(nn, deg, d, h, H + rb[i]);
    for (int i = 0; i < d && ok; i++) ok = addedge(nn, deg, d, ra[i], H + h);
    for (int v = 0; v < NN && ok; v++) if (deg[v] != d) ok = 0;
    free(ea); free(eb); free(rem); free(uA); free(uB); free(deg);
    if (!ok) { free(nn); return NULL; }
    return nn;
}

static void export_valid(void) {
    int h = vh, d = d_;
    int *ne = malloc(sizeof(int) * 2 * (size_t)h * d);
    int p = 0;
    for (int a = 0; a < h; a++)
        for (int j = 0; j < d; j++) {
            ne[2 * p] = a;
            ne[2 * p + 1] = vnb[a * d + j];
            p++;
        }
    free(bE);
    bE = ne;
    bEc = h * d;
    bestN = 2 * h;
}

/* Load the phase-1 graph (A-side edges listed first) as the valid start. */
static int init_from_bE(void) {
    int N = bestN, h = N / 2, d = d_;
    if (N < 2 || N % 2 != 0 || bEc != h * d) return 0;
    int *g = malloc(sizeof(int) * (size_t)N * d);
    int *deg = calloc((size_t)N, sizeof(int));
    int ok = 1;
    for (int p = 0; p < bEc && ok; p++) {
        int u = bE[2 * p], v = bE[2 * p + 1];
        if (u < 0 || v < 0 || u >= N || v >= N || (u < h) == (v < h)) ok = 0;
        else ok = addedge(g, deg, d, u, v);
    }
    for (int v = 0; v < N && ok; v++) if (deg[v] != d) ok = 0;
    free(deg);
    if (!ok) { free(g); return 0; }
    free(vnb);
    vnb = g;
    vh = h;
    return 1;
}

static void anneal_phase(double tend, int minN) {
    int d = d_;
    if (!(bestN > 0 && init_from_bE())) {
        /* No phase-1 graph: start from a circulant and repair it. */
        int h0 = minN / 2 + 1;
        if (h0 < d + 1) h0 = d + 1;
        int *g = malloc(sizeof(int) * (size_t)2 * h0 * d);
        for (int a = 0; a < h0; a++)
            for (int j = 0; j < d; j++) {
                g[a * d + j] = h0 + (a + j) % h0;
                g[(h0 + a) * d + j] = ((a - j) % h0 + h0) % h0;
            }
        an_nb = g;
        long long c = anneal_graph(h0, now() + 0.5 * (tend - now()));
        if (c == 0) {
            free(vnb);
            vnb = an_nb;
            vh = h0;
            an_nb = NULL;
            export_valid();
        } else {
            free(an_nb);
            an_nb = NULL;
            return;
        }
    }
    while (now() < tend) {
        double rem = tend - now();
        if (rem < 0.2) break;
        double slice = rem * 0.3;
        if (slice < 0.5) slice = rem;
        int hc = vh + 1;
        int *cand = an_expand(vnb, vh);
        if (!cand) continue;
        an_nb = cand;
        long long c = anneal_graph(hc, now() + slice);
        if (c == 0) {
            free(vnb);
            vnb = an_nb;
            vh = hc;
            an_nb = NULL;
            export_valid();
        } else {
            free(an_nb);
            an_nb = NULL;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (minN < 2) minN = 2;
    double split = (argc > 6) ? atof(argv[6]) : 0.7;
    if (split <= 0.0 || split >= 1.0) split = 0.7;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double tend = t0 + tl;
    group_phase(t0 + split * tl, minN);
    anneal_phase(tend, minN);

    if (bestN == 0 || bEc == 0) { printf("0 0\n"); return 0; }
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
    start = time.monotonic()
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

    # One C run: the group-lift search gets the first 70% of the budget and
    # then the annealing grow-and-repair phase starts from its best graph.
    # Every intermediate valid graph is kept, so the group result is the floor.
    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    elapsed = time.monotonic() - start
    budget = max(0.5, min(budget, time_limit - elapsed - 5.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1, 0.7],
                        timeout=budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

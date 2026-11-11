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
#define GMAX 2200
#define MAXDEG 16
#define HBITS 14
#define HSZ (1 << HBITS)

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
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m; if (b < 0) b += m;
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
static int cand[GMAX + 5];

/* ---------- group tables (any group of order <= GMAX, identity at index 0) ---------- */

static void finish_group(int G) {
    G_ = G;
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;   /* RS[s][g*s] = g */
}

/* Hash map from permutation code to element index, reset per closure by a stamp. */
static unsigned char PE[GMAX][MAXDEG];
static u64 HKEY[HSZ];
static int HVAL[HSZ];
static unsigned HST[HSZ];
static unsigned stamp = 0;

static unsigned hslot(u64 c) { return (unsigned)((c * 0x9E3779B97F4A7C15ULL) >> (64 - HBITS)); }
static int hfind(u64 c) {
    unsigned h = hslot(c);
    while (HST[h] == stamp) {
        if (HKEY[h] == c) return HVAL[h];
        h = (h + 1) & (HSZ - 1);
    }
    return -1;
}
static void hput(u64 c, int v) {
    unsigned h = hslot(c);
    while (HST[h] == stamp) h = (h + 1) & (HSZ - 1);
    HST[h] = stamp; HKEY[h] = c; HVAL[h] = v;
}
static u64 pcode(const unsigned char *p, int n) {
    u64 c = 0;
    for (int i = 0; i < n; i++) c |= (u64)p[i] << (4 * i);
    return c;
}
/* out = x then y, on n points; padding entries are zero. */
static void pmul(const unsigned char *x, const unsigned char *y, unsigned char *out, int n) {
    for (int i = 0; i < MAXDEG; i++) out[i] = (i < n) ? y[x[i]] : 0;
}

/* Closure of permutation generators on n <= 16 points. Returns |G| or 0 if it exceeds cap. */
static int perm_closure(unsigned char gens[][MAXDEG], int ng, int n, int cap) {
    unsigned char tmp[MAXDEG];
    stamp++;
    for (int i = 0; i < MAXDEG; i++) PE[0][i] = (i < n) ? (unsigned char)i : 0;
    hput(pcode(PE[0], n), 0);
    int G = 1;
    for (int qi = 0; qi < G; qi++)
        for (int g = 0; g < ng; g++) {
            pmul(PE[qi], gens[g], tmp, n);
            u64 c = pcode(tmp, n);
            if (hfind(c) >= 0) continue;
            if (G >= cap) return 0;
            memcpy(PE[G], tmp, MAXDEG);
            hput(c, G);
            G++;
        }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) {
            pmul(PE[x], PE[y], tmp, n);
            int idx = hfind(pcode(tmp, n));
            if (idx < 0) return 0;
            MT[x * G + y] = idx;
        }
    finish_group(G);
    return G;
}

/* Metacyclic group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e), element a*k2+b. */
static int build_meta(int m, int k2, int r) {
    int G = m * k2;
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    if (!pwr) return 0;
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
    free(pwr);
    finish_group(G);
    return 1;
}

static int pick_meta(int Gmin) {
    static const int K2s[18] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int k2 = K2s[rndi(18)];
    int m = (Gmin + k2 - 1) / k2;
    if (m < 2) m = 2;
    if (m * k2 > GMAX) return 0;
    int nc = 0;
    for (int r = 1; r < m; r++)
        if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
    if (nc == 0) return 0;
    return build_meta(m, k2, cand[rndi(nc)]);
}

static int primroot(int p) {
    for (int g = 2; g < p; g++) {
        int x = 1, ord = 0;
        do { x = x * g % p; ord++; } while (x != 1);
        if (ord == p - 1) return g;
    }
    return 1;
}

/* PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) acting on the p+1 points of the projective line. */
static int build_pslpgl(int p, int pgl, int cap) {
    int n = p + 1, INF = p;
    int g = primroot(p);
    unsigned char gens[3][MAXDEG];
    memset(gens, 0, sizeof gens);
    for (int x = 0; x < n; x++) {
        gens[0][x] = (unsigned char)(x == INF ? INF : (x + 1) % p);
        int s;
        if (x == INF) s = 0;
        else if (x == 0) s = INF;
        else s = (int)((p - powmod(x, p - 2, p)) % p);
        gens[1][x] = (unsigned char)s;
        gens[2][x] = (unsigned char)(x == INF ? INF : (x * g) % p);
    }
    return perm_closure(gens, pgl ? 3 : 2, n, cap) > 0;
}

static int pick_pslpgl(int Gmin, int cap) {
    static const int PP[4] = {5, 7, 11, 13};
    int start = rndi(8);
    for (int t = 0; t < 8; t++) {
        int idx = (start + t) % 8;
        int p = PP[idx / 2], pgl = idx % 2;
        if (build_pslpgl(p, pgl, cap) && G_ >= Gmin) return 1;
    }
    return 0;
}

/* Random 2- or 3-generated permutation subgroup of S_n, n in 5..9. */
static int build_random_perm(int Gmin, int cap) {
    unsigned char gens[3][MAXDEG];
    for (int att = 0; att < 300; att++) {
        int n = 5 + rndi(5), ng = 2 + rndi(2);
        memset(gens, 0, sizeof gens);
        for (int g = 0; g < ng; g++) {
            unsigned char arr[MAXDEG];
            for (int i = 0; i < n; i++) arr[i] = (unsigned char)i;
            for (int i = n - 1; i > 0; i--) {
                int j = rndi(i + 1);
                unsigned char t = arr[i]; arr[i] = arr[j]; arr[j] = t;
            }
            for (int i = 0; i < n; i++) gens[g][i] = arr[i];
        }
        int G = perm_closure(gens, ng, n, cap);
        if (G >= Gmin && G >= 4) return 1;
    }
    return 0;
}

/* ---------- lift state ---------- */

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

/* Cost = unreached (representative, vertex) pairs + heavy penalty for duplicate darts.
   Left multiplication is an automorphism, so block representatives suffice. */
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

/* Simulated annealing with iterated-local-search kicks. Returns 1 when cost is 0. */
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

    MT = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    RS = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    if (!MT || !RS) { printf("0 0\n"); return 0; }

    double tend = now() + tl;
    double slice = tl / 6.0;
    if (slice < 1.0) slice = 1.0;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};

    while (now() < tend) {
        int k = Ks[rndi(10)];
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 30 + 3);
        int cap = 2 * Gmin + 60;
        if (cap > GMAX) cap = GMAX;

        /* Family mix: metacyclic 30%, PSL/PGL(2,p) 35%, random permutation groups 35%. */
        int fam = rndi(100), ok;
        if (fam < 30) ok = pick_meta(Gmin);
        else if (fam < 65) ok = pick_pslpgl(Gmin, cap);
        else ok = build_random_perm(Gmin, cap);
        if (!ok) ok = pick_meta(Gmin);
        if (!ok) continue;

        K_ = k;
        alloc_state(2 * k * G_);
        double gend = now() + slice;
        if (gend > tend) gend = tend;
        int good = search(gend, 20000, 3000, 6);
        if (good && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            if (ne) {
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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    _ = time.monotonic() - start
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

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
#define PBUF_SIZE 8000

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

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;
static int Pbuf[PBUF_SIZE];
static int cand[PBUF_SIZE];

/* ---- group tables ----
   type 0: affine group Z_p^2 x| Z_e, element x = v*e + i (v in Z_p^2, v = v0*p+v1),
           (v,i)(w,j) = (v + P[i] w, i+j mod e), P[i] = 2x2 matrix block given by Pbuf.
   type 1: Heisenberg group mod p, element x = (a*p+b)*p+c,
           (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b').
   Identity is always element 0. */
static int build_table(int type, int p, int e) {
    int G = (type == 0) ? p * p * e : p * p * p;
    if (G < 1 || G > GMAX) return 0;
    G_ = G;
    for (int x = 0; x < G; x++) {
        if (type == 0) {
            int v = x / e, i = x % e;
            int v0 = v / p, v1 = v % p;
            const int *M = Pbuf + 4 * i;
            for (int y = 0; y < G; y++) {
                int w = y / e, j = y % e;
                int w0 = w / p, w1 = w % p;
                int t0 = (M[0] * w0 + M[1] * w1) % p;
                int t1 = (M[2] * w0 + M[3] * w1) % p;
                int s0 = (v0 + t0) % p, s1 = (v1 + t1) % p;
                MT[x * G + y] = (s0 * p + s1) * e + (i + j) % e;
            }
        } else {
            int a = x / (p * p), b = (x / p) % p, c = x % p;
            for (int y = 0; y < G; y++) {
                int a2 = y / (p * p), b2 = (y / p) % p, c2 = y % p;
                int na = (a + a2) % p, nbb = (b + b2) % p;
                int nc = (c + c2 + a * b2) % p;
                MT[x * G + y] = (na * p + nbb) * p + nc;
            }
        }
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
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
    int N = N_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G_] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[(size_t)l * N + v]];
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

/* Annealing with iterated-local-search kicks from the best state.
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

/* ---- 2x2 matrices mod p, stored as {m00, m01, m10, m11} ---- */
static void mat_mul(const int *A, const int *B, int p, int *C) {
    int t[4];
    t[0] = (A[0] * B[0] + A[1] * B[2]) % p;
    t[1] = (A[0] * B[1] + A[1] * B[3]) % p;
    t[2] = (A[2] * B[0] + A[3] * B[2]) % p;
    t[3] = (A[2] * B[1] + A[3] * B[3]) % p;
    memcpy(C, t, sizeof t);
}

static int mat_order(const int *M, int p, int cap) {
    int X[4] = {1 % p, 0, 0, 1 % p};
    for (int o = 1; o <= cap; o++) {
        mat_mul(X, M, p, X);
        if (X[0] == 1 % p && X[1] == 0 && X[2] == 0 && X[3] == 1 % p) return o;
    }
    return 0;
}

static void mat_pow(const int *M, int f, int p, int *R) {
    int X[4] = {1 % p, 0, 0, 1 % p};
    for (int t = 0; t < f; t++) mat_mul(X, M, p, X);
    memcpy(R, X, 4 * sizeof(int));
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

    double tend = now() + tl;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int HP[5] = {2, 3, 5, 7, 11};
    static const int AP[6] = {2, 3, 5, 7, 11, 13};

    while (now() < tend) {
        int k = Ks[rndi(10)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;

        if (rndu() < 0.3) {
            /* Heisenberg group mod p, order p^3. */
            int p = HP[rndi(5)];
            int G = p * p * p;
            if (G < Gmin || G > GMAX) continue;
            if (!build_table(1, p, 1)) continue;
        } else {
            /* Affine group Z_p^2 x| <M>, M in GL(2,p), group order p^2 * e with e | ord(M). */
            int p = AP[rndi(6)];
            int M[4], det = 0;
            for (int tr = 0; tr < 50 && det == 0; tr++) {
                for (int q = 0; q < 4; q++) M[q] = rndi(p);
                det = ((M[0] * M[3] - M[1] * M[2]) % p + p) % p;
            }
            if (det == 0) continue;
            int o = mat_order(M, p, 4000);
            if (o == 0) continue;
            int ne = 0;
            for (int e = 1; e <= o; e++) {
                if (o % e != 0) continue;
                int Gc = p * p * e;
                if (Gc >= Gmin && Gc <= GMAX) cand[ne++] = e;
            }
            if (ne == 0) continue;
            int e = cand[rndi(ne)];
            int Mp[4];
            mat_pow(M, o / e, p, Mp);
            Pbuf[0] = 1 % p; Pbuf[1] = 0; Pbuf[2] = 0; Pbuf[3] = 1 % p;
            for (int j = 1; j < e; j++) {
                int tmp[4];
                mat_mul(Pbuf + 4 * (j - 1), Mp, p, tmp);
                memcpy(Pbuf + 4 * j, tmp, sizeof tmp);
            }
            if (!build_table(0, p, e)) continue;
        }

        K_ = k;
        alloc_state(2 * k * G_);
        int ok = search(tend, 20000, 3000, 6);
        if (ok && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne2 = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne2[2 * p] = u;
                    ne2[2 * p + 1] = nb[(size_t)l * N_ + u];
                    p++;
                }
            free(bE);
            bE = ne2;
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

    # Almost the whole limit goes to the C search; the subprocess timeout sits a
    # few seconds after its internal budget so the case always finishes in time.
    budget = max(0.5, time_limit - 5.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

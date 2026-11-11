import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over semidirect products Z_m x| Z_k2.
#
# A lift has k blocks per side, each block a copy of G = m*k2 elements, and d
# layers. Layer l pairs A-block i with B-block sig[l][i] through voltage
# vol[l][i]: A(i,x) ~ B(j, x*s). Left multiplication by group elements is an
# automorphism, so the number of pairs at distance > D is G times the number of
# unreached (block-representative, vertex) pairs. Bitmask reach from the 2k
# representatives therefore gives the exact cost. A valid lift is a d-regular
# bipartite graph with 2kG vertices and diameter <= D.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_;
static int *mulT = NULL;
static int *sig = NULL, *vol = NULL, *nbr = NULL;
static u64 *ra = NULL, *rb = NULL;
static int *bEu = NULL, *bEv = NULL, bcap = 0;
static int best_n = 0, best_m = 0;

static long long lgcd(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
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

static void ensure_cap(int need) {
    if (need <= bcap) return;
    int nc = need + 16;
    int *a = realloc(bEu, sizeof(int) * (size_t)nc);
    int *b = realloc(bEv, sizeof(int) * (size_t)nc);
    if (!a || !b) { printf("0 0\n"); exit(0); }
    bEu = a;
    bEv = b;
    bcap = nc;
}

/* Multiplication table of Z_m x| Z_k2 with r^k2 = 1 mod m, element a*k2+b. */
static void build_group(int m, int k2, int r) {
    int G = m * k2;
    int *pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, dd = y % k2;
            long long aa = ((long long)a + (long long)pw[b] * c) % m;
            mulT[(size_t)x * G + y] = (int)(aa * k2 + (b + dd) % k2);
        }
    }
    free(pw);
}

static int sample_group(int Gt, int *mo, int *ko, int *ro) {
    static const int K2[16] = {1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10, 12};
    for (int t = 0; t < 300; t++) {
        int k2 = K2[rint_(16)];
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1 % m;
        if (k2 > 1) {
            int ok = 0;
            for (int c = 0; c < 60; c++) {
                int cand = 1 + rint_(m - 1);
                if (lgcd(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                    r = cand;
                    ok = 1;
                    break;
                }
            }
            if (!ok) continue;
        }
        *mo = m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

/* nbr[l*N + v]: layer-l neighbour of vertex v. A-blocks are 0..k-1, B-blocks k..2k-1. */
static void build_nbr(void) {
    int N = 2 * k_ * G_;
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) {
            int j = sig[l * k_ + i], s = vol[l * k_ + i];
            for (int x = 0; x < G_; x++) {
                int y = mulT[(size_t)x * G_ + s];
                nbr[(size_t)l * N + i * G_ + x] = (k_ + j) * G_ + y;
                nbr[(size_t)l * N + (k_ + j) * G_ + y] = i * G_ + x;
            }
        }
    }
}

/* Cost = sum over vertices of the number of block representatives that cannot
   reach them within D steps. Zero means valid. dup counts repeated darts. */
static long long eval_state(int *dup) {
    int N = 2 * k_ * G_;
    int full = 2 * k_;
    for (int v = 0; v < N; v++) ra[v] = 0;
    for (int b = 0; b < full; b++) ra[(size_t)b * G_] |= 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 r = ra[v];
            for (int l = 0; l < d_; l++) r |= ra[nbr[(size_t)l * N + v]];
            rb[v] = r;
            if (r != ra[v]) changed = 1;
        }
        u64 *t = ra; ra = rb; rb = t;
        if (!changed) break;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) tot += full - __builtin_popcountll(ra[v]);
    int dp = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (sig[l1 * k_ + i] == sig[l2 * k_ + i] && vol[l1 * k_ + i] == vol[l2 * k_ + i]) dp++;
    *dup = dp;
    return tot;
}

static void save_lift(int N) {
    int A = k_ * G_;
    ensure_cap(A * d_);
    int m = 0;
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d_; l++) {
            bEu[m] = u;
            bEv[m] = nbr[(size_t)l * N + u];
            m++;
        }
    best_n = N;
    best_m = m;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0 || n0 > 1000000) { printf("0 0\n"); return 0; }
    ensure_cap(m0 > 0 ? m0 : 1);
    int cnt = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        bEu[cnt] = u;
        bEv[cnt] = v;
        cnt++;
    }
    best_n = n0;
    best_m = cnt;
    if (n0 < 2) { best_n = 0; best_m = 0; }

    clock_t c0 = clock();
    double trial = limit / 10.0;
    if (trial > 3.0) trial = 3.0;
    if (trial < 0.5) trial = 0.5;
    static const int KS[5] = {1, 2, 2, 3, 4};
    const double T0 = 12.0, T1 = 0.3;
    const long long PEN = 12;

    while ((double)(clock() - c0) / CLOCKS_PER_SEC < limit - 0.05) {
        int k = KS[rint_(5)];
        int base = best_n / (2 * k);
        int Gt = base + 1 + rint_(base / 25 + 2);
        int m, k2, r;
        if (!sample_group(Gt, &m, &k2, &r)) continue;
        int G = m * k2;
        if (G > 2500 || 2 * k * G <= best_n) continue;
        int N = 2 * k * G;
        k_ = k;
        G_ = G;
        mulT = malloc(sizeof(int) * (size_t)G * G);
        sig = malloc(sizeof(int) * (size_t)d_ * k);
        vol = malloc(sizeof(int) * (size_t)d_ * k);
        nbr = malloc(sizeof(int) * (size_t)d_ * N);
        ra = malloc(sizeof(u64) * (size_t)N);
        rb = malloc(sizeof(u64) * (size_t)N);
        if (!mulT || !sig || !vol || !nbr || !ra || !rb) break;

        build_group(m, k2, r);
        for (int l = 0; l < d_; l++) {
            for (int i = 0; i < k; i++) sig[l * k + i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = sig[l * k + i];
                sig[l * k + i] = sig[l * k + j];
                sig[l * k + j] = t;
            }
            for (int i = 0; i < k; i++) vol[l * k + i] = rint_(G);
        }
        build_nbr();
        int dp = 0;
        long long e0 = eval_state(&dp);
        long long cur = e0 + PEN * dp;
        clock_t tstart = clock();

        while (cur != 0) {
            double tl = (double)(clock() - tstart) / CLOCKS_PER_SEC;
            double now = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (tl >= trial || now >= limit - 0.02) break;
            double T = T0 * pow(T1 / T0, tl / trial);

            int kind = (k >= 2 && rdbl() < 0.25);
            int l1 = 0, i1 = 0, i2 = 0, idx = 0, oldv = 0;
            if (kind) {
                l1 = rint_(d_);
                i1 = rint_(k);
                i2 = rint_(k - 1);
                if (i2 >= i1) i2++;
                int t = sig[l1 * k + i1];
                sig[l1 * k + i1] = sig[l1 * k + i2];
                sig[l1 * k + i2] = t;
            } else {
                idx = rint_(d_ * k);
                oldv = vol[idx];
                int nv = rint_(G);
                if (nv == oldv) continue;
                vol[idx] = nv;
            }

            build_nbr();
            int dp2 = 0;
            long long e2 = eval_state(&dp2);
            e2 += PEN * dp2;
            if (e2 <= cur || rdbl() < exp(-(double)(e2 - cur) / T)) {
                cur = e2;
            } else if (kind) {
                int t = sig[l1 * k + i1];
                sig[l1 * k + i1] = sig[l1 * k + i2];
                sig[l1 * k + i2] = t;
            } else {
                vol[idx] = oldv;
            }
        }

        /* The loop only exits with cur == 0 while nbr matches the accepted state. */
        if (cur == 0 && N > best_n) save_lift(N);

        free(mulT); mulT = NULL;
        free(sig); sig = NULL;
        free(vol); vol = NULL;
        free(nbr); nbr = NULL;
        free(ra); ra = NULL;
        free(rb); rb = NULL;
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bEu[i], bEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: edge-toggle annealer that grows a valid graph by vertex pairs.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int *bvCur, *bvNew;
static int best_n = 0, best_m = 0;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

static long long bad_pairs(int *out) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(r[w]);
        out[v] = N - pc;
        total += out[v];
    }
    return total;
}

static int pick_vertex(void) {
    if (rdbl() < 0.5) {
        for (int t = 0; t < 8; t++) {
            int v = rint_(N);
            if (bvCur[v] > 0) return v;
        }
    }
    return rint_(N);
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int grow_max = argc > 5 ? atoi(argv[5]) : 60;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = n0 + 2 * grow_max + 2;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bvCur = malloc(sizeof(int) * (size_t)cap_n);
    bvNew = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB || !bvCur || !bvNew) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
            }
        }
    }
    free(q);

    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    long long cost = bad_pairs(bvCur);
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = pick_vertex(), y = pick_vertex();
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs(bvNew);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            int *tp = bvCur; bvCur = bvNew; bvNew = tp;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _run_lift(d, D, seed, n, edges, seconds):
    """Run the C lift annealer; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}"],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C grow annealer from a valid graph; returns the parsed output."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    def left():
        return time_limit - (time.monotonic() - t0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: C bi-Cayley lift annealing over semidirect products.
    lift_secs = min(0.6 * time_limit, left() - 8.0)
    if lift_secs >= 1.0:
        try:
            n1, e1 = _run_lift(d, D, rng.randrange(1, 1 << 30), best[0], best[1], lift_secs)
            consider(n1, e1)
        except Exception:
            pass  # keep the valid fallback

    # Phase 2: C annealer grows the best valid graph by vertex pairs.
    grow_secs = left() - 6.0
    if grow_secs >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, grow_secs,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

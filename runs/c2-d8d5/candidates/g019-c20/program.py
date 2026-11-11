import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef long long ll;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int powmod(ll b, int e, int m) {
    ll r = 1 % m;
    b %= m; if (b < 0) b += m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return (int)r;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* ======================================================================
   Bi-Cayley lift engine (new).
   Group G = Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e).
   Base graph: k blocks on side A (0..k-1) and k on side B (k..2k-1); block
   x holds the |G| vertices x*G+g. Layer l joins A-block i to B-block
   lay[l][i] with voltage S[l][i]: (i,g) ~ (j, g*S). Every layer is a
   perfect matching of blocks, so the lift is d-regular on 2kG vertices.
   Left multiplication is an automorphism that is transitive on each block,
   so the graph has diameter <= D iff every vertex reaches every block
   representative (identity) within D steps. A bitset over the 2k blocks
   per vertex gives the cost in one pass.
   ====================================================================== */

static int L_d = 0, L_D = 0, L_k = 1, L_m = 2, L_k2 = 1, L_G = 2, L_r = 1;
static int L_pw[64];
static int *L_lay = NULL, *L_S = NULL, *L_nbr = NULL, *L_bu = NULL, *L_bv = NULL;
static u64 *L_rA = NULL, *L_rB = NULL, *L_reach = NULL, *L_reach2 = NULL;
static int L_capN = 0, L_capDK = 0, L_capE = 0;
static int L_bestN = 0, L_bestM = 0;

static int gmul(int x, int y) {
    int a1 = x / L_k2, b1 = x % L_k2, a2 = y / L_k2, b2 = y % L_k2;
    ll t = ((ll)a1 + (ll)L_pw[b1] * a2) % L_m;
    return (int)(t * L_k2 + (b1 + b2) % L_k2);
}

static int ginv(int x) {
    int a = x / L_k2, b = x % L_k2;
    int nb = (L_k2 - b) % L_k2;
    ll t = (-(ll)L_pw[nb] * a) % L_m;
    if (t < 0) t += L_m;
    return (int)(t * L_k2 + nb);
}

static int L_setup(int k, int m, int k2, int r) {
    L_k = k; L_m = m; L_k2 = k2; L_r = r; L_G = m * k2;
    L_pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) L_pw[b] = (int)(((ll)L_pw[b - 1] * r) % m);
    int NN = 2 * k * L_G;
    if (NN > L_capN) {
        free(L_rA); free(L_rB); free(L_nbr);
        L_rA = malloc(sizeof(u64) * (size_t)NN);
        L_rB = malloc(sizeof(u64) * (size_t)NN);
        L_nbr = malloc(sizeof(int) * (size_t)NN * L_d);
        if (!L_rA || !L_rB || !L_nbr) { L_capN = 0; return 0; }
        L_capN = NN;
    }
    int DK = L_d * k;
    if (DK > L_capDK) {
        free(L_lay); free(L_S);
        L_lay = malloc(sizeof(int) * DK);
        L_S = malloc(sizeof(int) * DK);
        if (!L_lay || !L_S) { L_capDK = 0; return 0; }
        L_capDK = DK;
    }
    return 1;
}

static int L_dup(void) {
    int k = L_k, tot = L_d * k, c = 0;
    for (int a = 0; a < tot; a++)
        for (int b = a + 1; b < tot; b++)
            if (a % k == b % k && L_lay[a] == L_lay[b] && L_S[a] == L_S[b]) c++;
    return c;
}

/* Cost: unreached (vertex, block) pairs plus a penalty per duplicate dart. */
static ll L_eval(void) {
    int k = L_k, G = L_G, d = L_d, NN = 2 * k * G;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = L_lay[l * k + i], s = L_S[l * k + i], si = ginv(s);
            for (int g = 0; g < G; g++) {
                L_nbr[(size_t)(i * G + g) * d + l] = (k + j) * G + gmul(g, s);
                L_nbr[(size_t)((k + j) * G + g) * d + l] = i * G + gmul(g, si);
            }
        }
    L_reach = L_rA; L_reach2 = L_rB;
    for (int v = 0; v < NN; v++) L_reach[v] = 0;
    for (int b = 0; b < 2 * k; b++) L_reach[(size_t)b * G] = 1ULL << b;
    for (int it = 0; it < L_D; it++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            u64 r0 = L_reach[v], x = r0;
            const int *nb = L_nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= L_reach[nb[l]];
            L_reach2[v] = x;
            if (x != r0) changed = 1;
        }
        u64 *t = L_reach; L_reach = L_reach2; L_reach2 = t;
        if (!changed) break;
    }
    ll unreached = 0;
    for (int v = 0; v < NN; v++) unreached += 2 * k - __builtin_popcountll(L_reach[v]);
    return unreached + 1000LL * (ll)L_dup();
}

static int L_anneal(int iters, int patience, clock_t deadline) {
    int k = L_k, d = L_d, G = L_G, DK = d * k;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) L_lay[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = L_lay[l * k + i]; L_lay[l * k + i] = L_lay[l * k + j]; L_lay[l * k + j] = t;
        }
    }
    for (int a = 0; a < DK; a++) L_S[a] = rint_(G);
    ll cost = L_eval();
    ll bestc = cost, c0 = cost > 1 ? cost : 1;
    double T0 = 0.02 * (double)c0;
    if (T0 < 1.0) T0 = 1.0;
    const double T1 = 0.3;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && clock() > deadline) break;
        double temp = T0 * pow(T1 / T0, (double)t / (double)iters);
        if (k >= 2 && rdbl() < 0.2) {
            int l = rint_(d);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int p1 = l * k + i1, p2 = l * k + i2;
            int tmp = L_lay[p1]; L_lay[p1] = L_lay[p2]; L_lay[p2] = tmp;
            ll c2 = L_eval();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) cost = c2;
            else { tmp = L_lay[p1]; L_lay[p1] = L_lay[p2]; L_lay[p2] = tmp; }
        } else {
            int a = rint_(DK);
            int old = L_S[a], nw = rint_(G);
            if (nw == old) continue;
            L_S[a] = nw;
            ll c2 = L_eval();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) cost = c2;
            else L_S[a] = old;
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return cost == 0;
}

static void L_save(void) {
    int k = L_k, d = L_d, G = L_G, cnt = d * k * G;
    if (cnt > L_capE) {
        free(L_bu); free(L_bv);
        L_bu = malloc(sizeof(int) * (size_t)cnt);
        L_bv = malloc(sizeof(int) * (size_t)cnt);
        if (!L_bu || !L_bv) { L_capE = 0; L_bestM = 0; return; }
        L_capE = cnt;
    }
    int m = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = L_lay[l * k + i], s = L_S[l * k + i];
            for (int g = 0; g < G; g++) {
                L_bu[m] = i * G + g;
                L_bv[m] = (k + j) * G + gmul(g, s);
                m++;
            }
        }
    L_bestN = 2 * k * G;
    L_bestM = m;
}

static const int K2OPTS[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12};

static int lift_main(int d, int D, int init_n, double limit) {
    L_d = d; L_D = D;
    clock_t deadline = clock() + (clock_t)(limit * CLOCKS_PER_SEC);
    int bestN = init_n;
    while (clock() < deadline) {
        int k = rint_(4) + 1;
        int base = bestN / (2 * k);
        int T = base + 1 + rint_(base / 10 + 2);
        if (T < 2) T = 2;
        int k2 = K2OPTS[rint_(12)];
        int m = (T + k2 - 1) / k2;
        int r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found && m >= 2; tr++) {
                int cand = (tr == 0 && k2 == 2 && m >= 3) ? m - 1 : 1 + rint_(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) { r = cand; found = 1; }
            }
            if (!found) { k2 = 1; m = T; r = 1; }
        }
        if (!L_setup(k, m, k2, r)) break;
        if (L_anneal(8000, 2500, deadline)) {
            L_save();
            if (L_bestM > 0 && L_bestN > bestN) bestN = L_bestN;
        }
    }
    if (L_bestM == 0 || L_bestN <= init_n) { printf("0 0\n"); return 0; }
    printf("%d %d\n", L_bestN, L_bestM);
    for (int i = 0; i < L_bestM; i++) printf("%d %d\n", L_bu[i], L_bv[i]);
    return 0;
}

/* ======================================================================
   Growth annealer: edge toggles with bitset ball expansion; grows by
   vertex pairs whenever the graph is valid.
   ====================================================================== */

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
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

static int grow_main(int d, int D, int grow_max, double limit) {
    d_ = d; D_ = D;
    if (grow_max < 0) grow_max = 0;
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000) { printf("0 0\n"); return 0; }
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
    int *queue = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB || !bvCur || !bvNew || !queue) {
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
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        queue[t++] = s;
        while (h < t) {
            int v = queue[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; queue[t++] = u; }
            }
        }
    }

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

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int mode = atoi(argv[5]);
    int extra = argc > 6 ? atoi(argv[6]) : 0;
    if (d < 1 || D < 1) { printf("0 0\n"); return 0; }
    if (mode == 0) return lift_main(d, D, extra, limit);
    return grow_main(d, D, extra, limit);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        # Araujo-Pardo & Lopez record for D = 3 when d - 2 is a prime power.
        if D == 3 and d >= 5 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Phase 1: C bi-Cayley lift search over Z_m x| Z_k2 (uses most of the budget).
    lift_end = t0 + max(1.0, 0.55 * time_limit - 2.0)
    budget = lift_end - time.monotonic()
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", 0, best[0]],
                            timeout=budget + 10.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass  # keep the valid fallback

    # Phase 2: C growth annealer adds vertex pairs to the best valid graph.
    grow_budget = time_limit - (time.monotonic() - t0) - 5.0
    if grow_budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, rng.randrange(1, 1 << 30), f"{grow_budget:.2f}", 1, 200],
                            stdin_graph=best, timeout=grow_budget + 10.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

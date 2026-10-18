import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift search over Z_m x|_r Z_k2 (fast, C-side BFS).
#
# Base graph: k blocks per side. Block i (side A) and block k+j (side B) each
# hold |G| vertices. Layer l (0..d-1) pairs A-block i with B-block perm[l][i]
# through voltage s = volt[l][i]:  (i, g) ~ (k + perm, g*s) for all g in G.
# Left multiplication by h is an automorphism, so distances from the 2k block
# identities determine all distances. Cost = unreached vertices summed over
# those 2k BFS sources, each limited to depth D. Cost 0 means valid.
# Parallel darts are harmless (they do not change distances) and are removed
# on output.
# ----------------------------------------------------------------------------

C_LIFT_SOURCE = r"""
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

static int d_, D_, k_, m_, k2_, G_, N_;
static long long *rpow_;
static int *perm_, *volt_, *nb_, *vis_, *queue_;
static int gen_ = 0;

static long long gcd_ll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

/* Element x = a*k2 + b means (a, b) in Z_m x|_r Z_k2. */
static int gmul(int x, int y) {
    long long a = x / k2_, b = x % k2_;
    long long c = y / k2_, e = y % k2_;
    long long ra = (a + rpow_[b] * c) % m_;
    long long rb = (b + e) % k2_;
    return (int)(ra * k2_ + rb);
}

/* Set the darts of layer l at A-block i, updating both endpoints of every edge. */
static void set_dart(int l, int i) {
    int p = perm_[l * k_ + i];
    int s = volt_[l * k_ + i];
    int Bbase = (k_ + p) * G_;
    for (int g = 0; g < G_; g++) {
        int h = gmul(g, s);
        int A = i * G_ + g;
        int B = Bbase + h;
        nb_[A * d_ + l] = B;
        nb_[B * d_ + l] = i * G_ + g;
    }
}

static long long cost_eval(void) {
    long long total = 0;
    int reps = 2 * k_;
    for (int r = 0; r < reps; r++) {
        if (++gen_ == 0x7fffffff) { memset(vis_, 0, sizeof(int) * (size_t)N_); gen_ = 1; }
        int head = 0, tail = 0;
        int src = r * G_;
        vis_[src] = gen_;
        queue_[tail++] = src;
        for (int lev = 0; lev < D_ && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int v = queue_[head++];
                const int *row = nb_ + (size_t)v * d_;
                for (int l = 0; l < d_; l++) {
                    int u = row[l];
                    if (vis_[u] != gen_) { vis_[u] = gen_; queue_[tail++] = u; }
                }
            }
        }
        total += N_ - tail;
    }
    return total;
}

static int fail_out(void) { printf("0 0\n"); return 0; }

static void emit(void) {
    int NA = k_ * G_;
    int cap = NA * d_;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    int *tmp = malloc(sizeof(int) * (size_t)d_);
    int cnt = 0;
    for (int v = 0; v < NA; v++) {
        for (int l = 0; l < d_; l++) tmp[l] = nb_[v * d_ + l];
        for (int a = 1; a < d_; a++) {
            int x = tmp[a], b = a - 1;
            while (b >= 0 && tmp[b] > x) { tmp[b + 1] = tmp[b]; b--; }
            tmp[b + 1] = x;
        }
        for (int l = 0; l < d_; l++) {
            if (l > 0 && tmp[l] == tmp[l - 1]) continue;
            eu[cnt] = v;
            ev[cnt] = tmp[l];
            cnt++;
        }
    }
    printf("%d %d\n", 2 * NA, cnt);
    for (int j = 0; j < cnt; j++) printf("%d %d\n", eu[j], ev[j]);
    free(eu);
    free(ev);
    free(tmp);
}

int main(int argc, char **argv) {
    if (argc < 9) return fail_out();
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    k_ = atoi(argv[3]);
    m_ = atoi(argv[4]);
    k2_ = atoi(argv[5]);
    long long r0 = atoll(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);
    if (d_ < 1 || d_ > 512 || D_ < 1 || k_ < 1 || m_ < 1 || k2_ < 1) return fail_out();
    if ((long long)m_ * k2_ > 300000) return fail_out();
    G_ = m_ * k2_;
    if (G_ < 2 || (long long)k_ * G_ > 300000) return fail_out();

    rpow_ = malloc(sizeof(long long) * (size_t)k2_);
    if (!rpow_) return fail_out();
    long long rr = r0 % m_;
    long long cur = 1 % m_;
    for (int b = 0; b < k2_; b++) { rpow_[b] = cur; cur = cur * rr % m_; }
    if (cur != 1 % m_) return fail_out();          /* need r^k2 = 1 mod m */
    if (gcd_ll(rr, m_) != 1) return fail_out();    /* need r a unit mod m */

    N_ = 2 * k_ * G_;
    perm_ = malloc(sizeof(int) * (size_t)(d_ * k_));
    volt_ = malloc(sizeof(int) * (size_t)(d_ * k_));
    nb_ = malloc(sizeof(int) * (size_t)N_ * d_);
    vis_ = calloc((size_t)N_, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)N_);
    if (!perm_ || !volt_ || !nb_ || !vis_ || !queue_) return fail_out();

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm_[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm_[l * k_ + i];
            perm_[l * k_ + i] = perm_[l * k_ + j];
            perm_[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) volt_[l * k_ + i] = rint_(G_);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++)
            set_dart(l, i);

    long long cost = cost_eval();
    int found = (cost == 0);
    clock_t c0 = clock();
    const double T0 = 4.0, T1 = 0.2;
    double frac = 0.0, T = T0;
    long long it = 0;

    while (!found) {
        if ((it & 15) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            frac = el / limit;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        if (k_ >= 2 && rdbl() < 0.25) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *p = perm_ + l * k_;
            int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                if (cost == 0) found = 1;
            } else {
                t = p[i1]; p[i1] = p[i2]; p[i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int idx = l * k_ + i1;
            int old = volt_[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            volt_[idx] = nv;
            set_dart(l, i1);
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                if (cost == 0) found = 1;
            } else {
                volt_[idx] = old;
                set_dart(l, i1);
            }
        }
    }

    if (!found) return fail_out();
    emit();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (unchanged).
# Starts from a valid graph, toggles cross-side pairs, and adds vertex pairs
# whenever the cost reaches zero.
# ----------------------------------------------------------------------------

C_GROW_SOURCE = r"""
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


def _sample_group(G_need, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with order m*k2 >= G_need. Always returns a valid triple."""
    k2 = rng.choice([1, 1, 2, 2, 3, 4, 4, 5, 6, 8, 10, 12])
    m = max(2, -(-G_need // k2))
    if k2 == 1:
        return m, 1, 1
    opts = [1]  # r = 1 gives the direct product, always valid
    if m > 2:
        if k2 % 2 == 0:
            opts.append(m - 1)  # r = -1 has order 2
        for _ in range(200):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                opts.append(c)
                break
    return m, k2, rng.choice(opts)


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift search; returns (n, edges), or (0, []) if no valid lift was found."""
    out = lib.run_c(C_LIFT_SOURCE, [d, D, k, m, k2, r, seed, f"{seconds:.2f}"],
                    timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C vertex-growing annealer from a valid graph; returns the parsed output."""
    out = lib.run_c(C_GROW_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 8.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2, safe fallback
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Phase 1: C lift search over semidirect products, with a bandit over base sizes k.
    lift_end = t0 + max(1.0, 0.68 * time_limit)
    KS = (1, 2, 3, 4, 5, 6)
    trials = {k: 0 for k in KS}
    wins = {k: 0 for k in KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(KS)
        return max(KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        step = max(2 * k, best[0] // 25)
        target = best[0] + step * (1 + rng.randrange(3))
        G_need = -(-target // (2 * k))
        m, k2, r = _sample_group(G_need, rng)
        slice_s = min(remaining, 3.0 + 3.0 * rng.random())
        trials[k] += 1
        try:
            n, e = _lift_in_c(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
        except Exception:
            continue
        if n > best[0]:
            wins[k] += 1
            consider(n, e)

    # Phase 2: C annealer grows the best valid graph by vertex pairs.
    grow_budget = (t0 + time_limit - 6.0) - time.monotonic()
    if grow_budget >= 1.0 and best[0] >= 4:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, grow_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

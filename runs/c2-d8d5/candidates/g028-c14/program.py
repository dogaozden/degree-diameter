import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW IDEA: orbit-reduced bi-Cayley annealer, run in C.
#
# A lift over the semidirect product G = Z_m x| Z_k2 (element a*k2+b, product
# (a,b)(c,e) = (a + r^b c, b + e)) has 2k "base" blocks of G vertices each. Left
# multiplication by G is an automorphism that fixes the blocks, so the lifted
# graph is vertex-transitive inside every block. Therefore the diameter is
# certified by BFS from only the 2k identity vertices, not from all 2kG vertices.
# Each evaluation costs about 2k BFS passes, so the C engine can test
# hundreds of thousands of voltage assignments per second. The search
# anneals over voltages S[l][i] and per-layer block permutations P[l].
# Targeted moves pick a base block that still has unreached vertices.
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
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

#define MAXK 8
#define PEN 50

static int d_, D_, k_, G_, m_, k2_, N_;
static int *Sv, *Pv, *Pinv, *invG, *pw, *nb, *mark, *queue, *bad, *curBad;
static int stampv = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(int b, int e, int m) {
    long long res = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) res = res * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)res;
}

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    long long aa = ((long long)a + (long long)pw[b] * c) % m_;
    int ee = (b + e) % k2_;
    return (int)aa * k2_ + ee;
}

/* Neighbour table of the lift. A-block i (ids i*G..) joins B-block j = Pv[l][i]
   through voltage s: (i,g) ~ (k+j, g*s). Each B vertex is joined back the same way. */
static void build_nb(void) {
    int G = G_, k = k_, d = d_;
    for (int i = 0; i < k; i++) {
        for (int g = 0; g < G; g++) {
            int u = i * G + g;
            for (int l = 0; l < d; l++) {
                int idx = l * k + i;
                int j = Pv[idx];
                nb[u * d + l] = (k + j) * G + gmul(g, Sv[idx]);
            }
        }
    }
    for (int j = 0; j < k; j++) {
        for (int h = 0; h < G; h++) {
            int u = (k + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = Pinv[l * k + j];
                int s = Sv[l * k + i];
                nb[u * d + l] = i * G + gmul(h, invG[s]);
            }
        }
    }
}

/* Number of vertices within distance D_ of src. */
static int bfs_reach(int src) {
    stampv++;
    if (stampv == 0x7fffffff) {
        memset(mark, 0, sizeof(int) * (size_t)N_);
        stampv = 1;
    }
    int head = 0, tail = 0;
    queue[tail++] = src;
    mark[src] = stampv;
    int level = 0;
    while (head < tail && level < D_) {
        int end = tail;
        while (head < end) {
            int u = queue[head++];
            const int *nu = nb + (size_t)u * d_;
            for (int l = 0; l < d_; l++) {
                int v = nu[l];
                if (mark[v] != stampv) {
                    mark[v] = stampv;
                    queue[tail++] = v;
                }
            }
        }
        level++;
    }
    return tail;
}

/* Cost = unreached pairs from the 2k base representatives + PEN * duplicate darts.
   Zero means the lift is valid, simple and has diameter <= D. */
static long long evaluate(void) {
    build_nb();
    long long unr = 0;
    for (int b = 0; b < 2 * k_; b++) {
        int reach = bfs_reach(b * G_);
        bad[b] = N_ - reach;
        unr += bad[b];
    }
    long long dups = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++) {
                int x = l * k_ + i, y = l2 * k_ + i;
                if (Pv[x] == Pv[y] && Sv[x] == Sv[y]) dups++;
            }
    return unr + PEN * dups;
}

static void swap_layer(int l, int a, int b) {
    int x = l * k_ + a, y = l * k_ + b;
    int t = Pv[x]; Pv[x] = Pv[y]; Pv[y] = t;
    Pinv[l * k_ + Pv[x]] = a;
    Pinv[l * k_ + Pv[y]] = b;
}

/* Prints the current lift (nb must match the current state). */
static void emit(void) {
    int M = k_ * G_ * d_;
    printf("%d %d\n", N_, M);
    for (int u = 0; u < k_ * G_; u++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", u, nb[u * d_ + l]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || D_ > 60 || k_ < 1 || k_ > MAXK ||
        m_ < 1 || m_ > 100000 || k2_ < 1 || k2_ > 100000) {
        printf("0 0\n");
        return 0;
    }
    long long Gl = (long long)m_ * k2_;
    if (Gl < 2 || Gl > 200000) { printf("0 0\n"); return 0; }
    G_ = (int)Gl;
    long long Nl = 2LL * k_ * G_;
    if (Nl > 2000000) { printf("0 0\n"); return 0; }
    N_ = (int)Nl;
    r = ((r % m_) + m_) % m_;
    if (gcd_(r, m_) != 1 || powmod_(r, k2_, m_) != 1 % m_) {
        printf("0 0\n");
        return 0;
    }

    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int t = 0; t < 10; t++) rnd();

    int G = G_, k = k_, d = d_;
    pw = malloc(sizeof(int) * k2_);
    pw[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw[t] = (int)((long long)pw[t - 1] * r % m_);
    invG = malloc(sizeof(int) * G);
    for (int g = 0; g < G; g++) {
        int a = g / k2_, b = g % k2_;
        int nbb = (k2_ - b) % k2_;
        long long na = (m_ - ((long long)pw[nbb] * a) % m_) % m_;
        invG[g] = (int)na * k2_ + nbb;
    }
    Sv = malloc(sizeof(int) * d * k);
    Pv = malloc(sizeof(int) * d * k);
    Pinv = malloc(sizeof(int) * d * k);
    nb = malloc(sizeof(int) * (size_t)N_ * d);
    mark = calloc((size_t)N_, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)N_);
    bad = malloc(sizeof(int) * 2 * k);
    curBad = malloc(sizeof(int) * 2 * k);
    if (!pw || !invG || !Sv || !Pv || !Pinv || !nb || !mark || !queue || !bad || !curBad) {
        printf("0 0\n");
        return 0;
    }

    int arr[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) arr[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = arr[i]; arr[i] = arr[j]; arr[j] = t;
        }
        for (int i = 0; i < k; i++) {
            Pv[l * k + i] = arr[i];
            Pinv[l * k + arr[i]] = i;
        }
        for (int i = 0; i < k; i++) Sv[l * k + i] = rint_(G);
    }

    clock_t c0 = clock();
    long long cost = evaluate();
    memcpy(curBad, bad, sizeof(int) * 2 * k);
    if (cost == 0) { emit(); return 0; }

    const double T0 = 3.0, T1 = 0.15;
    double T = T0;
    long long it = 0;
    while (1) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double ph = el / limit * 3.0;
            ph -= floor(ph);
            T = T0 * pow(T1 / T0, ph);
        }
        it++;

        int mv = 0, la = 0, ia = 0, ib = 0, oldS = 0, tgt = -1;
        if (k >= 2 && rdbl() < 0.15) {
            mv = 1;
            la = rint_(d);
            ia = rint_(k);
            ib = rint_(k - 1);
            if (ib >= ia) ib++;
            swap_layer(la, ia, ib);
        } else {
            if (rdbl() < 0.5) {
                int nz = 0;
                for (int b = 0; b < 2 * k; b++) if (curBad[b] > 0) nz++;
                if (nz > 0) {
                    int pick = rint_(nz);
                    for (int b = 0; b < 2 * k; b++) {
                        if (curBad[b] > 0) {
                            if (pick == 0) { tgt = b; break; }
                            pick--;
                        }
                    }
                }
            }
            if (tgt >= 0) {
                la = rint_(d);
                if (tgt < k) ia = tgt;
                else ia = Pinv[la * k + (tgt - k)];
            } else {
                la = rint_(d);
                ia = rint_(k);
            }
            int idx = la * k + ia;
            oldS = Sv[idx];
            int nv = rint_(G);
            if (nv == oldS) nv = (nv + 1) % G;
            Sv[idx] = nv;
        }

        long long nc = evaluate();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            memcpy(curBad, bad, sizeof(int) * 2 * k);
            if (cost == 0) { emit(); return 0; }
        } else {
            if (mv) swap_layer(la, ia, ib);
            else Sv[la * k + ia] = oldS;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Parent's C engine: edge-toggle annealer with vertex growth (used last).
# ----------------------------------------------------------------------------

GROW_C_SOURCE = r"""
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

_KS = (1, 2, 3, 4)
_LIFT_MAX_BUDGET = 6.0
_GROUP_CACHE = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups_in_range(lo, hi):
    """All semidirect groups Z_m x| Z_k2 (r^k2 = 1 mod m, gcd(r, m) = 1) with order in [lo, hi]."""
    key = (lo, hi)
    if key in _GROUP_CACHE:
        return _GROUP_CACHE[key]
    out = []
    for k2 in range(1, 41):
        m_lo = max(2, -(-lo // k2))
        m_hi = hi // k2
        for m in range(m_lo, m_hi + 1):
            if k2 == 1:
                out.append((m, 1, 1))
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    out.append((m, k2, r))
    _GROUP_CACHE[key] = out
    return out


def _lift_phase(d, D, best, rng, end):
    """Repeatedly call the C lift annealer on groups just above the current best order."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    fails = 0
    while True:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break
        if rng.random() < 0.15:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda c: (wins[c] + 1) / (trials[c] + 2) + 0.05 * rng.random())
        lo = best[0] // (2 * k) + 1
        slack = max(2, lo // 40) * (1 + fails // 4)
        cands = _groups_in_range(lo, lo + slack)
        if not cands:
            fails += 1
            continue
        m, k2, r = rng.choice(cands)
        budget = min(remaining - 0.5, _LIFT_MAX_BUDGET)
        if budget < 0.5:
            break
        trials[k] += 1
        try:
            out = lib.run_c(LIFT_C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            stdin_graph=None, timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            fails += 1
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            wins[k] += 1
            fails = 0
        else:
            fails += 1
    return best


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C growth annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(GROW_C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 5.0)
    return lib.parse_graph_text(out)


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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    T = float(time_limit)

    # Phase 1: C bi-Cayley lift search, growing the group order step by step.
    if d >= 2 and T > 4.0:
        try:
            best = _lift_phase(d, D, best, rng, t0 + 0.70 * T)
        except Exception:
            pass  # keep the valid fallback

    # Phase 2: C annealer grows the best valid graph by vertex pairs.
    grow_seconds = t0 + 0.93 * T - time.monotonic() - 0.5
    if grow_seconds >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, grow_seconds,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

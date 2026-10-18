import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine, two modes in one program:
#
#  * grow mode (argc 5 or 6): edge-toggle annealer with vertex growth. It starts
#    from a valid graph on stdin and adds vertex pairs while keeping diameter <= D.
#
#  * lift mode (argc 9): voltage-lift annealer over the semidirect product
#    Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e)) with k
#    base blocks per side. Vertex A(i,g) = i*G+g, B(j,h) = (k+j)*G+h, G = m*k2.
#    Layer l joins A(i,g) to B(perm_l(i), g*s_{l,i}). Each layer perm is a
#    bijection, so the graph is bipartite and d-regular up to duplicate darts.
#
#    NEW helper: left multiplication by any group element is an automorphism,
#    so a lift is vertex-transitive inside each block. The diameter test
#    therefore needs only 2k BFS runs (one from each block representative),
#    not N BFS runs. The annealer cost is the number of (representative, vertex)
#    pairs at distance > D, plus a penalty for duplicate darts.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
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

/* ============================ grow mode ============================ */

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
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

static long long bad_pairs(void) {
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
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt;
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

static int grow_main(int argc, char **argv) {
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
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB) {
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
    long long cost = bad_pairs();
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = rint_(N), y = rint_(N);
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
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

/* ============================ lift mode ============================ */

static int LD, LD2, Lk, Lk2, Lm, LG, LN, Lr;
static int *Lpw, *Lperm, *Lvolt, *Lnbr, *Ldist, *Lq;

/* (a,b)*(c,e) = (a + r^b c, b + e) in Z_m x| Z_k2, element coded a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / Lk2, b = x % Lk2;
    int c = y / Lk2, e = y % Lk2;
    long long t = (long long)Lpw[b] * c + a;
    int aa = (int)(t % Lm);
    int ee = (b + e) % Lk2;
    return aa * Lk2 + ee;
}

/* Fill the neighbour table: layer l joins A(i,g) to B(perm[l][i], g*s[l][i]). */
static void lift_build_nbr(void) {
    int d = LD, k = Lk, G = LG;
    for (int i = 0; i < k; i++) {
        for (int l = 0; l < d; l++) {
            int t = Lperm[l * k + i], s = Lvolt[l * k + i];
            for (int g = 0; g < G; g++) {
                int u = i * G + g;
                int w = (k + t) * G + gmul(g, s);
                Lnbr[u * d + l] = w;
                Lnbr[w * d + l] = u;
            }
        }
    }
}

/* Sum over the 2k block representatives of vertices at distance > LD2.
   Left multiplication is an automorphism, so these representatives suffice. */
static long long lift_cost(void) {
    int d = LD, N2 = LN, nsrc = 2 * Lk;
    lift_build_nbr();
    long long total = 0;
    for (int si = 0; si < nsrc; si++) {
        int src = si * LG;
        for (int v = 0; v < N2; v++) Ldist[v] = -1;
        int h = 0, t = 0, reached = 1;
        Lq[t++] = src;
        Ldist[src] = 0;
        while (h < t) {
            int v = Lq[h++];
            if (Ldist[v] >= LD2) continue;
            for (int l = 0; l < d; l++) {
                int u = Lnbr[v * d + l];
                if (Ldist[u] < 0) {
                    Ldist[u] = Ldist[v] + 1;
                    Lq[t++] = u;
                    reached++;
                }
            }
        }
        total += N2 - reached;
    }
    return total;
}

/* Number of duplicate darts (same target block and same voltage in two layers). */
static long long lift_dups(void) {
    long long c = 0;
    int d = LD, k = Lk;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (Lperm[l * k + i] == Lperm[l2 * k + i] &&
                    Lvolt[l * k + i] == Lvolt[l2 * k + i])
                    c++;
    return c;
}

static int lift_output(void) {
    lift_build_nbr();
    int d = LD, nA = Lk * LG;
    int cap = nA * d;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    int *tmp = malloc(sizeof(int) * (size_t)d);
    if (!eu || !ev || !tmp) return 0;
    int m = 0;
    for (int u = 0; u < nA; u++) {
        for (int l = 0; l < d; l++) tmp[l] = Lnbr[u * d + l];
        for (int a = 1; a < d; a++) {
            int x = tmp[a], b = a - 1;
            while (b >= 0 && tmp[b] > x) { tmp[b + 1] = tmp[b]; b--; }
            tmp[b + 1] = x;
        }
        for (int l = 0; l < d; l++) {
            if (l > 0 && tmp[l] == tmp[l - 1]) continue;
            eu[m] = u;
            ev[m] = tmp[l];
            m++;
        }
    }
    printf("%d %d\n", LN, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
    free(eu); free(ev); free(tmp);
    return 1;
}

static int lift_main(int argc, char **argv) {
    (void)argc;
    LD = atoi(argv[1]);
    LD2 = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    Lm = atoi(argv[5]);
    Lk2 = atoi(argv[6]);
    Lr = atoi(argv[7]);
    Lk = atoi(argv[8]);
    if (LD < 1 || LD2 < 1 || Lm < 2 || Lk2 < 1 || Lk < 1 || Lr < 0) {
        printf("0 0\n");
        return 0;
    }
    if ((long long)Lm * Lk2 > 4000 || Lk > 16 || LD > 64) {
        printf("0 0\n");
        return 0;
    }
    LG = Lm * Lk2;
    LN = 2 * Lk * LG;
    Lr %= Lm;
    {
        int x = Lr, y = Lm;
        while (y) { int t = x % y; x = y; y = t; }
        if (x != 1) { printf("0 0\n"); return 0; }
    }
    Lpw = malloc(sizeof(int) * (size_t)Lk2);
    Lperm = malloc(sizeof(int) * (size_t)LD * Lk);
    Lvolt = malloc(sizeof(int) * (size_t)LD * Lk);
    Lnbr = malloc(sizeof(int) * (size_t)LN * LD);
    Ldist = malloc(sizeof(int) * (size_t)LN);
    Lq = malloc(sizeof(int) * (size_t)LN);
    if (!Lpw || !Lperm || !Lvolt || !Lnbr || !Ldist || !Lq) {
        printf("0 0\n");
        return 0;
    }
    long long p = 1 % Lm;
    for (int b = 0; b < Lk2; b++) {
        Lpw[b] = (int)p;
        p = p * Lr % Lm;
    }
    if (p != 1 % Lm) { printf("0 0\n"); return 0; }

    for (int l = 0; l < LD; l++) {
        for (int i = 0; i < Lk; i++) Lperm[l * Lk + i] = i;
        for (int i = Lk - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = Lperm[l * Lk + i];
            Lperm[l * Lk + i] = Lperm[l * Lk + j];
            Lperm[l * Lk + j] = t;
        }
        for (int i = 0; i < Lk; i++) Lvolt[l * Lk + i] = rint_(LG);
    }

    const long long PEN = LG;
    long long cost = lift_cost() + PEN * lift_dups();
    double c0 = (double)(cost > 0 ? cost : 1);
    double T0 = 1.0 + 0.02 * c0, T1 = 0.2;
    int found = (cost == 0);

    clock_t cs = clock();
    while (!found) {
        double el = (double)(clock() - cs) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);
        int l = rint_(LD);

        if (Lk >= 2 && rint_(100) < 25) {
            /* swap the target blocks of two A-blocks in layer l (keeps the perm bijective) */
            int i1 = rint_(Lk), i2 = rint_(Lk - 1);
            if (i2 >= i1) i2++;
            int *pa = &Lperm[l * Lk + i1], *pb = &Lperm[l * Lk + i2];
            int t = *pa; *pa = *pb; *pb = t;
            long long nc = lift_cost() + PEN * lift_dups();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *pa; *pa = *pb; *pb = t;
            }
        } else {
            int i = rint_(Lk);
            int idx = l * Lk + i;
            int old = Lvolt[idx];
            int nv = rint_(LG);
            if (nv == old) continue;
            Lvolt[idx] = nv;
            long long nc = lift_cost() + PEN * lift_dups();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                Lvolt[idx] = old;
            }
        }
        if (cost == 0) found = 1;
    }

    if (found) {
        if (!lift_output()) printf("0 0\n");
    } else {
        printf("0 0\n");
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 9) return lift_main(argc, argv);
    return grow_main(argc, argv);
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_LIFT_KS = (1, 2, 3, 4, 5, 6)
_LIFT_SLICE = 6.0  # seconds per C lift attempt


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """2-colouring of the graph, or None if it is not bipartite."""
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


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cand = edges + [(v, n) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C edge-toggle grower from a valid graph; returns (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _lift_in_c(d, D, m, k2, r, k, seconds, seed):
    """Run the C voltage-lift annealer over Z_m x| Z_k2 with k blocks; returns (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", m, k2, r, k],
                    stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: C voltage-lift annealing. Each attempt targets a group whose
    # lift has more vertices than the current best. A bandit picks the base size k.
    lift_end = t0 + max(1.0, 0.8 * time_limit - 1.0)
    wins = {k: 0 for k in _LIFT_KS}
    trials = {k: 0 for k in _LIFT_KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_LIFT_KS)
        return max(_LIFT_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 2.0:
            break
        budget = min(_LIFT_SLICE, remaining)
        k = pick_k()
        g_min = best[0] // (2 * k) + 1          # 2*k*G > best[0]
        target = g_min + rng.randrange(0, max(1, g_min // 50 + 1))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        trials[k] += 1
        try:
            n, e = _lift_in_c(d, D, m, k2, r, k, budget, rng.randrange(1, 1 << 30))
        except Exception:
            continue
        if n > best[0]:
            wins[k] += 1
            consider(n, e)

    # Phase 2: use spare degree in the current best graph (cheap; often a no-op).
    slack_end = t0 + 0.85 * time_limit
    if time.monotonic() < slack_end - 1.0:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 3: C edge-toggle grower adds vertex pairs to the best valid graph.
    c_budget = time_limit - (time.monotonic() - t0) - 4.0
    if c_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, c_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

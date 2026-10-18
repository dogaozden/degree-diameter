"""Program: multi-orbit bi-Cayley (voltage) lifts over groups, searched by simulated annealing.

New idea versus the parent (single-orbit bi-Cayley A_x ~ B_{x s_k}):
  * Multi-orbit lift. Use NT orbits per side: vertices A_i x and B_j x, i, j < NT, x in G.
    Each A_i has d darts k. Dart (i,k) joins A_i x to B_{perm[k][i]} x*volt[i][k], where
    perm[k] is a permutation of [0,NT). Every B_j then has degree d, so the graph is d-regular
    and bipartite. Simplicity holds iff darts from A_i to the same B_j have distinct voltages.
  * Moves: change one voltage, or swap two entries of one permutation. Both are checked for
    multi-edges before the cost is evaluated.
  * Left multiplication by G is an automorphism, so the diameter check needs only 2*NT BFS
    sources (A_i e and B_j e). Cost = unreached (source, vertex) pairs.
  * Candidates are (group, NT) pairs with 2*NT*|G| in [vmin, Moore bound]. Groups are
    metacyclic Z_m x| Z_k and PSL/SL(2,q). The search runs an ascending pass (short slices)
    and then a descending pass for the largest feasible order.

Safety: C always prints a valid graph (K_{d,d} if nothing is found). Python checks the output
with lib.is_valid and keeps the valid fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley (voltage) lift search.
 * Vertices: A_i x (id i*N+x) and B_j x (id NT*N + j*N + x), i,j < NT, x in G.
 * Dart (i,k): A_i x ~ B_{perm[k][i]} (x * volt[i][k]).  perm[k] are permutations,
 * so each vertex has degree d. Simple iff darts from A_i to one B_j have distinct voltages.
 * Left multiplication is an automorphism, so BFS from A_i e and B_j e (2*NT sources) suffices.
 * Usage:  prog d D seed time_limit [vmin]     (stdin ignored)
 * Output: "n m" then m lines "u v".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 5000
#define MAXT 8
#define MAXDEG 8
#define MAXV (2 * MAXT * MAXN)
#define CYC 20000L
#define MAXC 512

typedef struct { int type, m, k, r, q, psl, N, NT, V; } Cand;

static int d, D, NT;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int pw_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------------ groups */

static uint16_t mt[(long)MAXN * MAXN];   /* mt[x*N+y] = x*y */
static int inv_[MAXN];
static int N, e_id;
static int pwv[MAXN];
static int keyidx[130321];               /* 19^4 */
static int elem[MAXN][4];

static int build_meta(int m, int k, int r) {
    long NN = (long)m * k;
    if (NN > MAXN - 1 || NN < 2) return 0;
    N = (int)NN;
    pwv[0] = 1 % m;
    for (int b = 1; b < k; b++) pwv[b] = (pwv[b - 1] * r) % m;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pwv[b] * c) % m;
            int bb = (b + dd) % k;
            mt[(long)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int ia = (m - (pwv[nb] * a) % m) % m;
        inv_[x] = ia * k + nb;
    }
    return 1;
}

static int build_matrix(int q, int psl) {
    int q4 = q * q * q * q;
    for (int i = 0; i < q4; i++) keyidx[i] = -1;
    N = 0;
    for (int p0 = 0; p0 < q; p0++)
    for (int p1 = 0; p1 < q; p1++)
    for (int p2 = 0; p2 < q; p2++)
    for (int p3 = 0; p3 < q; p3++) {
        if ((((p0 * p3 - p1 * p2) % q) + q) % q != 1) continue;
        int key = ((p0 * q + p1) * q + p2) * q + p3;
        if (keyidx[key] != -1) continue;
        if (N >= MAXN) return 0;
        elem[N][0] = p0; elem[N][1] = p1; elem[N][2] = p2; elem[N][3] = p3;
        keyidx[key] = N;
        if (psl) {
            int n0 = (q - p0) % q, n1 = (q - p1) % q;
            int n2 = (q - p2) % q, n3 = (q - p3) % q;
            keyidx[((n0 * q + n1) * q + n2) * q + n3] = N;
        }
        N++;
    }
    e_id = keyidx[((1 * q + 0) * q + 0) * q + 1];
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int a = elem[x][0], b = elem[x][1], c = elem[x][2], e = elem[x][3];
            int a2 = elem[y][0], b2 = elem[y][1], c2 = elem[y][2], e2 = elem[y][3];
            int c00 = (a * a2 + b * c2) % q;
            int c01 = (a * b2 + b * e2) % q;
            int c10 = (c * a2 + e * c2) % q;
            int c11 = (c * b2 + e * e2) % q;
            mt[(long)x * N + y] = (uint16_t)keyidx[((c00 * q + c01) * q + c10) * q + c11];
        }
    for (int x = 0; x < N; x++) {
        inv_[x] = -1;
        for (int y = 0; y < N; y++)
            if (mt[(long)x * N + y] == e_id) { inv_[x] = y; break; }
    }
    return 1;
}

static int build_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static Cand curG;
static int haveG = 0;

static int same_group(const Cand *a, const Cand *b) {
    if (a->type != b->type) return 0;
    if (a->type == 0) return a->m == b->m && a->k == b->k && a->r == b->r;
    return a->q == b->q && a->psl == b->psl;
}

/* Build (or reuse) the group of candidate c; returns 1 if it has exactly c->N elements. */
static int ensure_group(const Cand *c) {
    if (haveG && same_group(&curG, c)) return N == c->N;
    haveG = 0;
    if (!build_cand(c)) return 0;
    curG = *c;
    haveG = 1;
    return N == c->N;
}

/* ------------------------------------------------------------------ lift state */

static int perm[MAXDEG][MAXT];    /* dart (i,k) goes to B_{perm[k][i]} */
static int pinv[MAXDEG][MAXT];    /* pinv[k][j] = i with perm[k][i] = j */
static int volt[MAXT][MAXDEG];    /* voltage of dart (i,k) */
static int vinv[MAXT][MAXDEG];    /* inverse voltage */
static int bestPerm[MAXDEG][MAXT], bestVolt[MAXT][MAXDEG];
static int foundPerm[MAXDEG][MAXT], foundVolt[MAXT][MAXDEG];

static void rebuild_k(int k) {
    for (int i = 0; i < NT; i++) pinv[k][perm[k][i]] = i;
}

static void rebuild_all(void) {
    for (int k = 0; k < d; k++) rebuild_k(k);
    for (int i = 0; i < NT; i++)
        for (int k = 0; k < d; k++) vinv[i][k] = inv_[volt[i][k]];
}

/* 1 if dart (i,k) clashes with an earlier dart k2<k from A_i to the same B_j with equal voltage. */
static int conflict_prev(int i, int k) {
    for (int k2 = 0; k2 < k; k2++)
        if (perm[k2][i] == perm[k][i] && volt[i][k2] == volt[i][k]) return 1;
    return 0;
}

/* 1 if A_i has no multi-edge. */
static int ok_side(int i) {
    for (int k = 0; k < d; k++)
        for (int k2 = k + 1; k2 < d; k2++)
            if (perm[k][i] == perm[k2][i] && volt[i][k] == volt[i][k2]) return 0;
    return 1;
}

static void random_state(void) {
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < NT; i++) perm[k][i] = i;
        for (int i = NT - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[k][i]; perm[k][i] = perm[k][j]; perm[k][j] = tmp;
        }
    }
    for (int i = 0; i < NT; i++)
        for (int k = 0; k < d; k++) {
            do volt[i][k] = rndint(N); while (conflict_prev(i, k));
        }
    rebuild_all();
}

static void save_best(void) {
    memcpy(bestPerm, perm, sizeof perm);
    memcpy(bestVolt, volt, sizeof volt);
}

static void load_best(void) {
    memcpy(perm, bestPerm, sizeof perm);
    memcpy(volt, bestVolt, sizeof volt);
    rebuild_all();
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int TN = NT * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < TN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int j = perm[k][i];
                    int u = TN + j * N + mt[(long)x * N + volt[i][k]];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int rel = v - TN, j = rel / N, y = rel - j * N;
                for (int k = 0; k < d; k++) {
                    int i = pinv[k][j];
                    int u = i * N + mt[(long)y * N + vinv[i][k]];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    long V = 2L * NT * N;
    long c = 0;
    for (int s = 0; s < 2 * NT; s++) {
        int src = (s < NT) ? s * N + e_id : NT * N + (s - NT) * N + e_id;
        c += V - ball(src, D);
    }
    return c;
}

/* ------------------------------------------------------------------ annealing */

static double T0 = 4.0, T1 = 0.3;

/* Returns 1 with a zero-cost lift in perm/volt, or 0 on timeout. */
static int anneal(double until) {
    random_state();
    long cur = cost_now(), best = cur;
    save_best();
    while (best > 0) {
        for (long it = 0; it < CYC; it++) {
            if ((it & 127) == 0 && now() > until) return 0;
            double Tm = T0 * pow(T1 / T0, (double)it / (double)CYC);
            if (NT > 1 && rnd01() < 0.15) {
                /* permutation move: swap the targets of two A-vertices on layer k */
                int k = rndint(d), i = rndint(NT), i2 = rndint(NT - 1);
                if (i2 >= i) i2++;
                int a = perm[k][i], b = perm[k][i2];
                perm[k][i] = b; perm[k][i2] = a; rebuild_k(k);
                if (!ok_side(i) || !ok_side(i2)) {
                    perm[k][i] = a; perm[k][i2] = b; rebuild_k(k);
                    continue;
                }
                long nc = cost_now();
                long delta = nc - cur;
                if (delta <= 0 || rnd01() < exp(-(double)delta / Tm)) {
                    cur = nc;
                    if (cur < best) { best = cur; save_best(); if (best == 0) return 1; }
                } else {
                    perm[k][i] = a; perm[k][i2] = b; rebuild_k(k);
                }
            } else {
                /* voltage move on one dart */
                int i = rndint(NT), k = rndint(d), x = rndint(N);
                int old = volt[i][k];
                if (x == old) continue;
                volt[i][k] = x; vinv[i][k] = inv_[x];
                if (!ok_side(i)) {
                    volt[i][k] = old; vinv[i][k] = inv_[old];
                    continue;
                }
                long nc = cost_now();
                long delta = nc - cur;
                if (delta <= 0 || rnd01() < exp(-(double)delta / Tm)) {
                    cur = nc;
                    if (cur < best) { best = cur; save_best(); if (best == 0) return 1; }
                } else {
                    volt[i][k] = old; vinv[i][k] = inv_[old];
                }
            }
        }
        load_best();      /* restart the cycle from the best state so far */
        cur = best;
    }
    return 1;
}

/* ------------------------------------------------------------------ candidates & output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static int pick_meta(int n, int *pm, int *pk, int *pr) {
    int cnt = 0;
    for (int m = 3; m <= n / 3; m++) {
        if (n % m) continue;
        int k = n / m;
        if (k < 3) continue;
        for (int r = 2; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (pw_mod(r, k, m) != 1) continue;
            cnt++;
            if (rndint(cnt) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
    return cnt;
}

static int cmp_cand(const void *a, const void *b) {
    int x = ((const Cand *)a)->V, y = ((const Cand *)b)->V;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [vmin]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long vmin = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    static Cand cs[MAXC];
    int nc = 0;

    /* metacyclic groups over a grid of orders, for every orbit count NT */
    for (int nt = 1; nt <= MAXT; nt++) {
        long Nlo = (vmin + 2L * nt - 1) / (2L * nt);
        if (Nlo < d) Nlo = d;
        if (Nlo < 3) Nlo = 3;
        long Nhi = moore / (2L * nt);
        if (Nhi > MAXN - 1) Nhi = MAXN - 1;
        if (Nhi < Nlo) continue;
        long step = (Nhi - Nlo) / 16;
        if (step < 1) step = 1;
        for (long nv = Nlo; nv <= Nhi && nc < MAXC; nv += step) {
            int pm = 0, pk = 0, pr = 0;
            if (pick_meta((int)nv, &pm, &pk, &pr) > 0) {
                cs[nc++] = (Cand){0, pm, pk, pr, 0, 0, (int)nv, nt, (int)(2L * nt * nv)};
            }
        }
    }
    /* PSL(2,q) and SL(2,q) groups */
    static const int qs[6] = {5, 7, 11, 13, 17, 19};
    for (int qi = 0; qi < 6; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long ord = q * (q * q - 1);
            if (psl) ord /= 2;
            if (ord > MAXN - 1 || ord < d) continue;
            for (int nt = 1; nt <= MAXT; nt++) {
                long V = 2L * nt * ord;
                if (V < vmin || V > moore || nc >= MAXC) continue;
                cs[nc++] = (Cand){1, 0, 0, 0, (int)q, psl, (int)ord, nt, (int)V};
            }
        }
    if (nc == 0) { print_complete(); return 0; }
    qsort(cs, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestIdx = -1;
    long bestV = 0;

    /* Phase A: ascending sweep with short slices, to get a feasible baseline. */
    double tA = now() + 0.4 * (t_end - now());
    for (int c = 0; c < nc; c++) {
        if (now() > tA) break;
        if (cs[c].V <= bestV) continue;
        double slice = tA - now();
        if (slice > 1.0) slice = 1.0;
        if (slice < 0.3) break;
        if (!ensure_group(&cs[c])) continue;
        NT = cs[c].NT;
        if (anneal(now() + slice)) {
            bestV = cs[c].V;
            bestIdx = c;
            memcpy(foundPerm, perm, sizeof perm);
            memcpy(foundVolt, volt, sizeof volt);
        }
    }

    /* Phase B: descending sweep, largest orders first; stop at the first success. */
    for (int c = nc - 1; c >= 0; c--) {
        if (cs[c].V <= bestV) break;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = rem < 2.5 ? rem : 2.5;
        if (!ensure_group(&cs[c])) continue;
        NT = cs[c].NT;
        if (anneal(now() + slice)) {
            bestV = cs[c].V;
            bestIdx = c;
            memcpy(foundPerm, perm, sizeof perm);
            memcpy(foundVolt, volt, sizeof volt);
            break;
        }
    }

    if (bestIdx < 0) {
        print_complete();
        return 0;
    }
    ensure_group(&cs[bestIdx]);
    NT = cs[bestIdx].NT;
    memcpy(perm, foundPerm, sizeof perm);
    memcpy(volt, foundVolt, sizeof volt);
    rebuild_all();

    int V = 2 * NT * N;
    printf("%d %ld\n", V, (long)NT * N * d);
    for (int i = 0; i < NT; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int u = i * N + x;
                int v = NT * N + perm[k][i] * N + mt[(long)x * N + volt[i][k]];
                printf("%d %d\n", u, v);
            }
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    moore = lib.moore_bound(d, D)
    # Only search for graphs strictly larger than the start when we have one.
    vmin = best[0] + 1 if start is not None else max(2, int(0.2 * moore))
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if best[0] >= moore:
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vmin],
                             timeout=budget + 10)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best

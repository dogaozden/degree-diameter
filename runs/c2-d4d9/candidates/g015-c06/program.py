"""Program: voltage lifts of multi-vertex bipartite base graphs over metacyclic groups.

Construction (new in this version):
  * Base graph: P vertices A_0..A_{P-1} and P vertices B_0..B_{P-1}, d-regular, with
    d permutations sigma_k (A_i -> B_{sigma_k(i)}) and a voltage g_{i,k} in G per dart.
  * Lift: vertex (A_i, x) is adjacent to (B_{sigma_k(i)}, x*g_{i,k}) for k < d.
    The lift is bipartite, d-regular, and has 2*P*|G| vertices.
  * Left multiplication by G is an automorphism, so diameter <= D holds iff BFS from
    (A_i, e) and (B_j, e) reaches every vertex within D steps, for all base vertices.
  * Search: simulated-descent hill climbing on the number of unreached pairs. Moves change
    one voltage or swap two images of one permutation. Duplicate edges are never created.
  * Groups: cyclic and metacyclic Z_m x|_r Z_k, with P in {1,2,3,4}. P = 1 is the old
    bi-Cayley family. Larger P gives a different search space with the same order range.
  * Scheduling: iterative deepening over candidates sorted by vertex count (largest first).

Safety: Python validates the C output with lib.is_valid and keeps the best valid graph,
falling back to a known construction or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 8
#define MAXP 4
#define MAXN 3200
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 40
#define STALL 6000

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GN;
static int pwv[MAXN], rpv[MAXN];
static uint16_t TB[MAXN * MAXN];
static int INVG[MAXN];

static int gmul_f(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int aa = (a + pwv[b] * c) % GM;
    int bb = (b + e) % GK;
    return aa * GK + bb;
}

#define GMUL(x, y) ((int)TB[(size_t)(x) * GN + (y)])

static int set_group(int m, int k, int r) {
    if (m < 2 || k < 1 || m * k > MAXN) return 0;
    GM = m;
    GK = k;
    GN = m * k;
    int rinv = 1 % m;
    if (k > 1) {
        rinv = -1;
        for (int t = 1; t < m; t++) {
            if ((long)t * r % m == 1) { rinv = t; break; }
        }
        if (rinv < 0) return 0;
    }
    pwv[0] = 1 % m;
    rpv[0] = 1 % m;
    for (int b = 1; b < k; b++) {
        pwv[b] = (int)((long)pwv[b - 1] * r % m);
        rpv[b] = (int)((long)rpv[b - 1] * rinv % m);
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            TB[(size_t)x * GN + y] = (uint16_t)gmul_f(x, y);
    for (int x = 0; x < GN; x++) {
        int a = x / GK, b = x - a * GK;
        int nb = (GK - b) % GK;
        int na = (GM - (int)((long)rpv[b] * a % GM)) % GM;
        INVG[x] = na * GK + nb;
    }
    return 1;
}

/* ------------------------------------------------------------ lift state */

static int P;
static int sig[MAXD][MAXP];
static int sinv[MAXD][MAXP];
static int gv[MAXP][MAXD];

static int dup_ok(int i) {
    for (int k1 = 0; k1 < d; k1++)
        for (int k2 = k1 + 1; k2 < d; k2++)
            if (sig[k1][i] == sig[k2][i] && gv[i][k1] == gv[i][k2]) return 0;
    return 1;
}

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int bfs_reach(int src) {
    int half = P * GN;
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < half) {
                int i = v / GN, x = v - i * GN;
                for (int k = 0; k < d; k++) {
                    int j = sig[k][i];
                    int u = half + j * GN + GMUL(x, gv[i][k]);
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / GN, y = w - j * GN;
                for (int k = 0; k < d; k++) {
                    int i = sinv[k][j];
                    int x = GMUL(y, INVG[gv[i][k]]);
                    int u = i * GN + x;
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    int NV = 2 * P * GN, half = P * GN;
    long c = 0;
    for (int i = 0; i < P; i++) {
        c += (long)(NV - bfs_reach(i * GN));
        c += (long)(NV - bfs_reach(half + i * GN));
    }
    return c;
}

static int random_config(void) {
    for (int k = 0; k < d; k++) {
        int p[MAXP];
        for (int i = 0; i < P; i++) p[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int t = rndint(i + 1);
            int tmp = p[i]; p[i] = p[t]; p[t] = tmp;
        }
        for (int i = 0; i < P; i++) {
            sig[k][i] = p[i];
            sinv[k][p[i]] = i;
        }
    }
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++)
            gv[i][k] = rndint(GN);
    for (int attempt = 0; attempt < 5000; attempt++) {
        int bad = 0;
        for (int i = 0; i < P; i++) {
            if (!dup_ok(i)) {
                bad = 1;
                for (int k = 0; k < d; k++) gv[i][k] = rndint(GN);
            }
        }
        if (!bad) return 1;
    }
    return 0;
}

static long climb(double until) {
    if (!random_config()) return 0;
    long cur = cost_now(), best = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL) {
            if (!random_config()) return 0;
            cur = cost_now();
            best = cur;
            stall = 0;
            continue;
        }
        if (P >= 2 && rndint(3) == 0) {
            int k = rndint(d);
            int i = rndint(P);
            int i2 = rndint(P - 1);
            if (i2 >= i) i2++;
            int a = sig[k][i], b2 = sig[k][i2];
            sig[k][i] = b2; sig[k][i2] = a;
            sinv[k][b2] = i; sinv[k][a] = i2;
            if (!dup_ok(i) || !dup_ok(i2)) {
                sig[k][i] = a; sig[k][i2] = b2;
                sinv[k][a] = i; sinv[k][b2] = i2;
                continue;
            }
            long nc = cost_now();
            if (nc <= cur || rnd01() < 0.01) {
                cur = nc;
            } else {
                sig[k][i] = a; sig[k][i2] = b2;
                sinv[k][a] = i; sinv[k][b2] = i2;
            }
        } else {
            int i = rndint(P), k = rndint(d);
            int old = gv[i][k];
            int ng = rndint(GN);
            if (ng == old) continue;
            gv[i][k] = ng;
            if (!dup_ok(i)) { gv[i][k] = old; continue; }
            long nc = cost_now();
            if (nc <= cur || rnd01() < 0.01) cur = nc;
            else gv[i][k] = old;
        }
        if (cur < best) { best = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int m, k, r, P, N;
    long V;
} Cand;

static Cand cands[MAXCAND];
static int ncand = 0;

static void add_cand(int m, int k, int r, int Pv, int N) {
    if (ncand >= MAXCAND) return;
    Cand c;
    c.m = m; c.k = k; c.r = r; c.P = Pv; c.N = N;
    c.V = 2L * Pv * N;
    cands[ncand++] = c;
}

static void add_groups(int Pv, int N) {
    add_cand(N, 1, 1, Pv, N);   /* cyclic */
    int chosen = 0, seen = 0;
    int cm[2], ck[2], cr[2];
    for (int k = 2; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m < 3) continue;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            seen++;
            if (chosen < 2) {
                cm[chosen] = m; ck[chosen] = k; cr[chosen] = r;
                chosen++;
            } else {
                int j = rndint(seen);
                if (j < 2) { cm[j] = m; ck[j] = k; cr[j] = r; }
            }
        }
    }
    for (int c = 0; c < chosen; c++) add_cand(cm[c], ck[c], cr[c], Pv, N);
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static int bm, bk, br, bP;
static int bsig[MAXD][MAXP];
static int bgv[MAXP][MAXD];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lo] [ref]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = argc > 5 ? atol(argv[5]) : 0;
    long ref = argc > 6 ? atol(argv[6]) : lo;
    if (lo < 0) lo = 0;
    if (ref < lo) ref = lo;
    if (ref < 1) ref = 1;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();

    ncand = 0;
    for (int Pv = 1; Pv <= MAXP; Pv++) {
        long N1 = ref / (2L * Pv) + 1;
        for (long N = N1; N >= N1 - 1; N--) {
            if (N < 3 || N > MAXN) continue;
            long V = 2L * Pv * N;
            if (V <= lo || V > moore) continue;
            if (d > N) continue;
            add_groups(Pv, (int)N);
        }
    }
    /* sort candidates by vertex count, largest first */
    for (int i = 1; i < ncand; i++) {
        Cand key = cands[i];
        int j = i - 1;
        while (j >= 0 && cands[j].V < key.V) {
            cands[j + 1] = cands[j];
            j--;
        }
        cands[j + 1] = key;
    }

    int have = 0;
    long bestV = lo;
    double budget0 = t_end - now();
    double base = budget0 * 0.015;
    if (base < 0.2) base = 0.2;

    for (int round = 0; round < 6; round++) {
        for (int c = 0; c < ncand; c++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *cd = &cands[c];
            if (cd->V <= bestV) continue;
            if (!set_group(cd->m, cd->k, cd->r)) continue;
            P = cd->P;
            double slice = base * (double)(1 << round);
            if (slice > rem) slice = rem;
            if (climb(now() + slice)) {
                have = 1;
                bestV = cd->V;
                bm = cd->m; bk = cd->k; br = cd->r; bP = cd->P;
                memcpy(bsig, sig, sizeof sig);
                memcpy(bgv, gv, sizeof gv);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!set_group(bm, bk, br)) { print_complete(); return 0; }
    P = bP;
    memcpy(sig, bsig, sizeof sig);
    memcpy(gv, bgv, sizeof gv);
    for (int k = 0; k < d; k++)
        for (int i = 0; i < P; i++)
            sinv[k][sig[k][i]] = i;
    if (cost_now() != 0) { print_complete(); return 0; }

    int NV = 2 * P * GN, half = P * GN;
    printf("%d %d\n", NV, P * GN * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < GN; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * GN + x, half + sig[k][i] * GN + GMUL(x, gv[i][k]));
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


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
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d} fallback
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it
    ref = REF_VERTICES.get((d, D), best[0])
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0], ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best

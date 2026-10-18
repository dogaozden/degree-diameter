"""Bi-Cayley lift search in C over semidirect groups Z_m x| Z_k, with a bandit over base sizes.

The lift search moved into C. Each candidate is a bipartite voltage lift of a base with
kb vertices per side over a group of order G, with d perfect matchings (layers) and one
voltage per dart. Group transitivity on blocks lets one bitmask BFS of D rounds check
the diameter. Simulated annealing repairs voltages and permutations until the diameter
is at most D. Every returned graph is checked with lib.is_valid. Fallbacks are K_{d,d},
projective planes, and known constructions.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXNN 60000
#define MAXK 16
#define PEN 1000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long long moore_cap(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2LL * D;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000LL) break;
    }
    return 2 * s;
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

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Current lift: base sizes KB, group Z_GM x| Z_GK with r = GR, order GO = GM*GK. */
static int KB, GM, GK, GR, GO, NN;
static uint64_t FULL;
static int *PW, *Pm, *IP, *Sv, *nbr;     /* nbr[l*NN + v] */
static uint64_t *ACC, *CAND, *TMPB;
static int *bestnbr;
static int bestN = 0, bestK = 0, bestG = 0;

/* (a,b)*(c,e) = (a + r^b c, b + e), element coded a*GK + b. */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, e = y % GK;
    long long t = (long long)PW[b] * c;
    int aa = (int)((a + t) % GM);
    int bb = (b + e) % GK;
    return aa * GK + bb;
}

/* Dart (layer l, base i): A_{i,g} ~ B_{P[l][i], g*s}; sets both directions. */
static void set_dart(int l, int i) {
    int p = Pm[l * MAXK + i], s = Sv[l * MAXK + i];
    int *nb = nbr + (size_t)l * NN;
    for (int g = 0; g < GO; g++) {
        int a = i * GO + g;
        int b = (KB + p) * GO + gmul(g, s);
        nb[a] = b;
        nb[b] = a;
    }
}

/* Number of (base, layer pair) duplicate darts (same neighbour block and voltage). */
static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < KB; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (Pm[l1 * MAXK + i] == Pm[l2 * MAXK + i] &&
                    Sv[l1 * MAXK + i] == Sv[l2 * MAXK + i])
                    dup++;
    return dup;
}

/* Fills out[v] with the set of blocks whose representative is within D of v; returns unreached count. */
static long eval_into(uint64_t *out) {
    int N = NN;
    uint64_t *cur = out, *nxt = TMPB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * KB; b++) cur[(size_t)b * GO] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *tp = cur;
        cur = nxt;
        nxt = tp;
        if (!changed) break;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint64_t) * (size_t)N);
    long cost = 0;
    for (int v = 0; v < N; v++) cost += 2 * KB - __builtin_popcountll(out[v]);
    return cost;
}

static void swap_perm(int l, int i1, int i2) {
    int *P = Pm + l * MAXK, *I = IP + l * MAXK;
    int t = P[i1];
    P[i1] = P[i2];
    P[i2] = t;
    I[P[i1]] = i1;
    I[P[i2]] = i2;
    set_dart(l, i1);
    set_dart(l, i2);
}

static void random_state(void) {
    int arr[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KB; i++) arr[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = arr[i];
            arr[i] = arr[j];
            arr[j] = t;
        }
        for (int i = 0; i < KB; i++) {
            Pm[l * MAXK + i] = arr[i];
            IP[l * MAXK + arr[i]] = i;
            Sv[l * MAXK + i] = rndint(GO);
        }
        for (int i = 0; i < KB; i++) set_dart(l, i);
    }
}

/* Simulated annealing on voltages and matchings. Returns cost (0 = valid lift in nbr). */
static long anneal(double deadline, long iters, long patience) {
    random_state();
    long cost = eval_into(ACC) + PEN * dupcount();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (KB >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(KB);
            int i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            swap_perm(l, i1, i2);
            long c2 = eval_into(CAND) + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                uint64_t *tp = ACC;
                ACC = CAND;
                CAND = tp;
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                swap_perm(l, i1, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tries = 0; tries < 30; tries++) {
                int u = rndint(NN);
                if (ACC[u] != FULL) { v = u; break; }
            }
            if (v >= 0) {
                int blk = v / GO;
                l = rndint(d);
                i = (blk < KB) ? blk : IP[l * MAXK + (blk - KB)];
            }
        }
        if (l < 0) {
            l = rndint(d);
            i = rndint(KB);
        }
        int *sp = &Sv[l * MAXK + i];
        int old = *sp;
        int nw = rndint(GO);
        if (nw == old) continue;
        *sp = nw;
        set_dart(l, i);
        long c2 = eval_into(CAND) + PEN * dupcount();
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
            uint64_t *tp = ACC;
            ACC = CAND;
            CAND = tp;
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            *sp = old;
            set_dart(l, i);
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit best_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long best_n0 = atol(argv[5]);
    double deadline = now() + limit - 0.3;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > 64 || D < 3) { printf("0 0\n"); return 0; }
    long long cap = moore_cap();
    if (cap > MAXNN) cap = MAXNN;
    if (cap <= best_n0) { printf("0 0\n"); return 0; }

    nbr = malloc(sizeof(int) * (size_t)d * MAXNN);
    Pm = malloc(sizeof(int) * (size_t)d * MAXK);
    IP = malloc(sizeof(int) * (size_t)d * MAXK);
    Sv = malloc(sizeof(int) * (size_t)d * MAXK);
    bestnbr = malloc(sizeof(int) * (size_t)d * MAXNN);
    PW = malloc(sizeof(int) * MAXNN);
    int *cands = malloc(sizeof(int) * MAXNN);
    ACC = malloc(sizeof(uint64_t) * MAXNN);
    CAND = malloc(sizeof(uint64_t) * MAXNN);
    TMPB = malloc(sizeof(uint64_t) * MAXNN);
    if (!nbr || !Pm || !IP || !Sv || !bestnbr || !PW || !cands || !ACC || !CAND || !TMPB) {
        printf("0 0\n");
        return 0;
    }

    long wins[MAXK + 1] = {0}, trials[MAXK + 1] = {0};
    double goal = (double)best_n0 * 1.05 + 2.0;

    while (now() < deadline) {
        int kb = 1;
        if (rnd01() < 0.2) {
            kb = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            for (int k = 1; k <= MAXK; k++) {
                double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; kb = k; }
            }
        }
        long long kk = 2LL * kb;
        long long gt = (long long)ceil(goal / (double)kk) + rndint(3);
        if (kk * gt <= best_n0) gt = best_n0 / kk + 1;
        if (kk * gt > cap) gt = cap / kk;
        if (gt < 2 || kk * gt <= best_n0) {
            goal = (double)best_n0 * 1.02 + 1.0;
            continue;
        }

        /* Group order Gv = gt; pick a subgroup split Gv = GM * GK with GM >= 2. */
        long long Gv = gt;
        long long cnt = 0;
        for (long long x = 1; x <= Gv / 2; x++)
            if (Gv % x == 0) cnt++;
        long long pick = rndint((int)cnt);
        long long k2 = 1, c = 0;
        for (long long x = 1; x <= Gv / 2; x++) {
            if (Gv % x == 0) {
                if (c == pick) { k2 = x; break; }
                c++;
            }
        }
        GO = (int)Gv;
        GK = (int)k2;
        GM = (int)(Gv / k2);

        GR = 1;
        if (GK >= 2 && GM >= 3) {
            int nc = 0;
            cands[nc++] = 1;
            for (int r = 2; r < GM; r++)
                if (gcdll(r, GM) == 1 && powmod(r, GK, GM) == 1 % GM) cands[nc++] = r;
            GR = cands[rndint(nc)];
        }
        PW[0] = 1 % GM;
        for (int b = 1; b < GK; b++) PW[b] = (int)((long long)PW[b - 1] * GR % GM);

        KB = kb;
        NN = 2 * KB * GO;
        FULL = (1ULL << (2 * KB)) - 1ULL;

        trials[kb]++;
        long cost = anneal(deadline, 30000, 4000);
        if (cost == 0) {
            wins[kb]++;
            if (NN > bestN) {
                bestN = NN;
                bestK = KB;
                bestG = GO;
                memcpy(bestnbr, nbr, sizeof(int) * (size_t)d * NN);
            }
            if (NN * 1.04 > goal) goal = NN * 1.04;
        } else {
            double bn = bestN > best_n0 ? (double)bestN : (double)best_n0;
            double g2 = goal * 0.99;
            goal = (g2 > bn * 1.02) ? g2 : bn * 1.02;
        }
    }

    if (bestN > best_n0) {
        int A = bestK * bestG;
        long m = (long)A * d;
        printf("%d %ld\n", bestN, m);
        for (int u = 0; u < A; u++)
            for (int l = 0; l < d; l++)
                printf("%d %d\n", u, bestnbr[(size_t)l * bestN + u]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best
    if D == 2:
        return best  # K_{d,d} is optimal here

    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            if D == 3 and lib.is_prime_power(d - 1) and best_n == pg[0]:
                return best
    except Exception:
        pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() - t0 < 0.1 * time_limit:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C lift annealer over semidirect groups, all of the budget.
    total = 0.82 * time_limit - 4.0
    remaining = t0 + total - time.monotonic()
    if remaining > 2.0 and d <= 64:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             timeout=remaining + 8.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    return best

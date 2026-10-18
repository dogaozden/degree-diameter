import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New idea: group-symmetric lift annealer in C.
#
# A bi-Cayley lift over a group G of order GO has 2*BK*GO vertices. Left
# multiplication by any h in G is an automorphism, so the number of vertices
# within distance D of every vertex is determined by the 2*BK block
# representatives (b, identity). Each annealing step therefore needs only
# 2*BK BFS runs, not one per vertex. The state is a d-regular base multigraph
# (per-layer permutations lay[l][i] and voltages vol[l][i]). Moves change a
# voltage, which is aimed at an unreached block half the time, or swap two
# entries of a layer permutation. Cost = unreached (source, target) block pairs.
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
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rnd_int(int n) { return (int)(rnd64() % (u64)n); }
static double rnd_dbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

#define PEN 40LL

static int d_, D_, BK, GM, GK, GR, GO, NV;
static int *mulT, *invT, *lay, *vol, *pinv, *nbr, *mark, *qu, *cand;
static int stampc = 1;
static int badv = -1;

static void rebuild_pinv(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < BK; i++)
            pinv[l * BK + lay[l * BK + i]] = i;
}

static void rebuild_nbr(void) {
    for (int i = 0; i < BK; i++)
        for (int g = 0; g < GO; g++)
            for (int l = 0; l < d_; l++) {
                int j = lay[l * BK + i];
                int s = vol[l * BK + i];
                nbr[(i * GO + g) * d_ + l] = (BK + j) * GO + mulT[g * GO + s];
            }
    for (int j = 0; j < BK; j++)
        for (int h = 0; h < GO; h++)
            for (int l = 0; l < d_; l++) {
                int i = pinv[l * BK + j];
                int s = vol[l * BK + i];
                nbr[((BK + j) * GO + h) * d_ + l] = i * GO + mulT[h * GO + invT[s]];
            }
}

static long long dupcount(void) {
    long long c = 0;
    for (int i = 0; i < BK; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (lay[l1 * BK + i] == lay[l2 * BK + i] &&
                    vol[l1 * BK + i] == vol[l2 * BK + i])
                    c++;
    return c;
}

/* Cost = sum over the 2*BK block representatives of unreached vertices, plus
   a penalty for repeated darts. Zero means the lift is valid. */
static long long evalcost(void) {
    rebuild_pinv();
    rebuild_nbr();
    long long c = 0;
    for (int b = 0; b < 2 * BK; b++) {
        int src = b * GO;
        stampc++;
        int head = 0, tail = 0;
        qu[tail++] = src;
        mark[src] = stampc;
        for (int lvl = 0; lvl < D_ && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int v = qu[head++];
                const int *nb = nbr + (size_t)v * d_;
                for (int l = 0; l < d_; l++) {
                    int u = nb[l];
                    if (mark[u] != stampc) { mark[u] = stampc; qu[tail++] = u; }
                }
            }
        }
        int un = NV - tail;
        c += un;
        cand[b] = -1;
        if (un > 0) {
            int r0 = rnd_int(NV);
            for (int t = 0; t < NV; t++) {
                int v = r0 + t;
                if (v >= NV) v -= NV;
                if (mark[v] != stampc) { cand[b] = v; break; }
            }
        }
    }
    int ncand = 0;
    for (int b = 0; b < 2 * BK; b++) if (cand[b] >= 0) ncand++;
    badv = -1;
    if (ncand > 0) {
        int pick = rnd_int(ncand);
        for (int b = 0; b < 2 * BK; b++) {
            if (cand[b] >= 0) {
                if (pick == 0) { badv = cand[b]; break; }
                pick--;
            }
        }
    }
    return c + PEN * dupcount();
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    BK = atoi(argv[3]);
    GM = atoi(argv[4]);
    GK = atoi(argv[5]);
    GR = atoi(argv[6]);
    u64 seed = strtoull(argv[7], NULL, 10);
    double limit = atof(argv[8]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();

    if (d_ < 1 || d_ > 64 || D_ < 1 || BK < 1 || GM < 1 || GK < 1 || GR < 0) {
        printf("0 0\n");
        return 0;
    }
    GO = GM * GK;
    if (GO < 1 || GO > 4000) { printf("0 0\n"); return 0; }
    NV = 2 * BK * GO;
    if (NV > 20000) { printf("0 0\n"); return 0; }
    GR %= GM;

    /* Check r^GK = 1 mod GM. */
    int *pw = malloc(sizeof(int) * GK);
    long long x = 1 % GM;
    for (int t = 0; t < GK; t++) {
        pw[t] = (int)x;
        x = (x * GR) % GM;
    }
    if (x != 1 % GM) { printf("0 0\n"); return 0; }

    /* Multiplication table of Z_GM x| Z_GK, element a*GK+b. */
    mulT = malloc(sizeof(int) * (size_t)GO * GO);
    invT = malloc(sizeof(int) * GO);
    for (int p = 0; p < GO; p++) {
        int a1 = p / GK, b1 = p % GK;
        for (int q = 0; q < GO; q++) {
            int a2 = q / GK, b2 = q % GK;
            long long a = ((long long)a1 + (long long)pw[b1] * a2) % GM;
            int b = (b1 + b2) % GK;
            mulT[p * GO + q] = (int)(a * GK + b);
        }
    }
    for (int p = 0; p < GO; p++) {
        int found = -1;
        for (int q = 0; q < GO && found < 0; q++)
            if (mulT[p * GO + q] == 0) found = q;
        if (found < 0) { printf("0 0\n"); return 0; }
        invT[p] = found;
    }

    lay = malloc(sizeof(int) * d_ * BK);
    vol = malloc(sizeof(int) * d_ * BK);
    pinv = malloc(sizeof(int) * d_ * BK);
    nbr = malloc(sizeof(int) * (size_t)NV * d_);
    mark = calloc(NV, sizeof(int));
    qu = malloc(sizeof(int) * NV);
    cand = malloc(sizeof(int) * 2 * BK);

    /* Random d-regular base: each layer is a permutation of the BK B-vertices. */
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < BK; i++) lay[l * BK + i] = i;
        for (int i = BK - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = lay[l * BK + i];
            lay[l * BK + i] = lay[l * BK + j];
            lay[l * BK + j] = t;
        }
        for (int i = 0; i < BK; i++) vol[l * BK + i] = rnd_int(GO);
    }

    long long cur = evalcost();
    clock_t c0 = clock();
    double T = 3.0, el = 0.0;
    long long it = 0;
    while (cur != 0) {
        if ((it & 127) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = 3.0 * pow(0.05 / 3.0, el / limit);
        }
        it++;
        if (BK >= 2 && rnd_dbl() < 0.15) {
            int l = rnd_int(d_);
            int i1 = rnd_int(BK);
            int i2 = rnd_int(BK - 1);
            if (i2 >= i1) i2++;
            int a = l * BK + i1, b = l * BK + i2;
            int t = lay[a]; lay[a] = lay[b]; lay[b] = t;
            long long nc = evalcost();
            long long delta = nc - cur;
            if (delta <= 0 || rnd_dbl() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                t = lay[a]; lay[a] = lay[b]; lay[b] = t;
            }
        } else {
            int l, i;
            if (badv >= 0 && rnd_dbl() < 0.5) {
                rebuild_pinv();
                int blk = badv / GO;
                l = rnd_int(d_);
                if (blk < BK) i = blk;
                else i = pinv[l * BK + (blk - BK)];
            } else {
                l = rnd_int(d_);
                i = rnd_int(BK);
            }
            int idx = l * BK + i;
            int old = vol[idx];
            int nw = rnd_int(GO);
            if (nw == old) continue;
            vol[idx] = nw;
            long long nc = evalcost();
            long long delta = nc - cur;
            if (delta <= 0 || rnd_dbl() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                vol[idx] = old;
            }
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    int nA = BK * GO;
    printf("%d %d\n", NV, nA * d_);
    for (int v = 0; v < nA; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[v * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36]
_BK_CHOICES = (1, 2, 3, 4, 5, 6)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            if k2 == 2 and m > 2 and rng.random() < 0.4:
                c = m - 1
                if math.gcd(c, m) == 1 and pow(c, 2, m) == 1 % m:
                    r = c
            if r is None and m > 2:
                for _ in range(80):
                    c = rng.randrange(2, m)
                    if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                        r = c
                        break
            if r is None:
                r = 1  # direct product: always a valid group
        return m, k2, r
    return None


def _lift_in_c(d, D, bk, m, k2, r, seed, seconds):
    """Run the C lift annealer; returns (n, deduplicated edges), or (0, []) on failure."""
    out = lib.run_c(C_SOURCE, [d, D, bk, m, k2, r, seed, f"{seconds:.2f}"],
                    stdin_graph=None, timeout=seconds + 15.0)
    n, e = lib.parse_graph_text(out)
    edges = sorted({(min(u, v), max(u, v)) for u, v in e if u != v})
    return n, edges


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

    # Exact construction (calibration case returns immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Lift search: order-targeting bandit over base sizes, C annealer per try.
    search_end = t0 + max(0.5, min(time_limit - 5.0, 0.92 * time_limit))
    trials = {k: 0 for k in _BK_CHOICES}
    wins = {k: 0 for k in _BK_CHOICES}

    def pick_bk():
        if rng.random() < 0.2:
            return rng.choice(_BK_CHOICES)
        return max(_BK_CHOICES,
                   key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = search_end - time.monotonic()
        if remaining < 1.0:
            break
        bk = pick_bk()
        n_now = best[0]
        go_min = -(-(n_now + 2) // (2 * bk))  # smallest group order that beats best
        slack = rng.randrange(0, go_min // 80 + 2)
        g = _sample_group(go_min + slack, rng)
        if g is None:
            continue
        m, k2, r = g
        slice_s = min(remaining, max(4.0, min(12.0, remaining / 2.0)))
        trials[bk] += 1
        try:
            n2, e2 = _lift_in_c(d, D, bk, m, k2, r, rng.randrange(1, 1 << 30), slice_s)
        except Exception:
            break  # keep the valid fallback
        before = best[0]
        if n2 > 0:
            consider(n2, e2)
        if best[0] > before:
            wins[bk] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

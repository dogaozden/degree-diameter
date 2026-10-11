import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of semidirect products.
#
# Group: Z_m x|_r Z_k2, element x = a*k2 + b, with (a,b)(c,d) = (a + r^b c, b + d).
# Base: K A-vertices and K B-vertices. Layer l is a permutation p_l of the base,
# and dart (l, i) joins A_i to B_{p_l(i)} with voltage s. Every vertex has degree DD.
# Moves: change one voltage, or swap two B-targets inside a layer (keeps degrees).
# Left multiplication is an automorphism, so the diameter test only needs BFS from
# the 2K representatives A_i,1 and B_j,1.
# Cost = number of unreached (representative, vertex) pairs; 0 means valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000L

static int K, G, DD, DIAM, NV, ND;
static int *MUL;
static int *Di, *Dj, *Ds;
static int *adj, *cnt, *dist, *queue;

static void build_mul(int m, int k2, int r) {
    int *pw = malloc(sizeof(int) * k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int ra = (int)((a + (long long)pw[b] * c) % m);
            MUL[x * G + y] = ra * k2 + (b + e) % k2;
        }
    }
    free(pw);
}

static long cost_of(void) {
    int a, b;
    for (a = 0; a < ND; a++)
        for (b = a + 1; b < ND; b++)
            if (Di[a] == Di[b] && Dj[a] == Dj[b] && Ds[a] == Ds[b]) return BIGC;
    memset(cnt, 0, sizeof(int) * NV);
    for (int x = 0; x < ND; x++) {
        int i = Di[x], j = Dj[x], s = Ds[x];
        for (int g = 0; g < G; g++) {
            int va = i * G + g;
            int vb = (K + j) * G + MUL[g * G + s];
            adj[va * DD + cnt[va]++] = vb;
            adj[vb * DD + cnt[vb]++] = va;
        }
    }
    long total = 0;
    for (int rp = 0; rp < 2 * K; rp++) {
        int src = (rp < K) ? rp * G : (K + (rp - K)) * G;
        for (int v = 0; v < NV; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        queue[tail++] = src;
        while (head < tail) {
            int u = queue[head++];
            if (dist[u] >= DIAM) continue;
            for (int t = 0; t < DD; t++) {
                int v = adj[u * DD + t];
                if (v >= 0 && dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    queue[tail++] = v;
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    int m = atoi(argv[4]), k2 = atoi(argv[5]), r = atoi(argv[6]);
    unsigned long seed = strtoul(argv[7], NULL, 10);
    double tl = atof(argv[8]);
    G = m * k2;
    NV = 2 * K * G;
    ND = DD * K;
    srand((unsigned)seed);

    MUL = malloc(sizeof(int) * G * G);
    build_mul(m, k2, r);

    Di = malloc(sizeof(int) * ND);
    Dj = malloc(sizeof(int) * ND);
    Ds = malloc(sizeof(int) * ND);
    adj = malloc(sizeof(int) * NV * DD);
    cnt = malloc(sizeof(int) * NV);
    dist = malloc(sizeof(int) * NV);
    queue = malloc(sizeof(int) * NV);
    int *BJ = malloc(sizeof(int) * ND);
    int *BS = malloc(sizeof(int) * ND);
    int *perm = malloc(sizeof(int) * K);

    for (int l = 0; l < DD; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int q = rand() % (i + 1);
            int t = perm[i]; perm[i] = perm[q]; perm[q] = t;
        }
        for (int i = 0; i < K; i++) {
            Di[l * K + i] = i;
            Dj[l * K + i] = perm[i];
            Ds[l * K + i] = rand() % G;
        }
    }

    long cur = cost_of();
    long bestc = cur;
    memcpy(BJ, Dj, sizeof(int) * ND);
    memcpy(BS, Ds, sizeof(int) * ND);

    clock_t t0 = clock();
    double frac = 0.0, T0 = 2.0;
    unsigned long it = 0;
    while (bestc > 0) {
        if ((it & 127UL) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
            frac = el / tl;
        }
        it++;
        int type = 0, x1 = 0, x2 = 0, oldS = 0;
        if (K == 1 || rand() % 10 < 6) {
            type = 0;
            x1 = rand() % ND;
            oldS = Ds[x1];
            Ds[x1] = rand() % G;
        } else {
            type = 1;
            int l = rand() % DD;
            int i1 = rand() % K;
            int i2 = rand() % (K - 1);
            if (i2 >= i1) i2++;
            x1 = l * K + i1;
            x2 = l * K + i2;
            int tmp = Dj[x1]; Dj[x1] = Dj[x2]; Dj[x2] = tmp;
        }
        long c2 = cost_of();
        double T = T0 * (1.0 - frac) + 0.05;
        int accept = 0;
        if (c2 <= cur) accept = 1;
        else {
            double u = (double)rand() / ((double)RAND_MAX + 1.0);
            if (u < exp(-(double)(c2 - cur) / T)) accept = 1;
        }
        if (accept) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(BJ, Dj, sizeof(int) * ND);
                memcpy(BS, Ds, sizeof(int) * ND);
            }
        } else {
            if (type == 0) {
                Ds[x1] = oldS;
            } else {
                int tmp = Dj[x1]; Dj[x1] = Dj[x2]; Dj[x2] = tmp;
            }
        }
    }

    if (bestc == 0) {
        printf("%d %d\n", NV, ND * G);
        for (int x = 0; x < ND; x++) {
            int i = Di[x];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + BJ[x]) * G + MUL[g * G + BS[x]];
                printf("%d %d\n", a, b);
            }
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python glue for the C annealer.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k2, r) with Z_m x|_r Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        return m, k2, r
    return None


def _run_group(d, D, k, m, k2, r, seed, budget):
    """Run the C annealer for one group. Returns (n, edges); n == 0 means no valid lift found."""
    args = [d, D, k, m, k2, r, seed, f"{budget:.3f}"]
    out = lib.run_c(C_SOURCE, args, stdin_graph=None, timeout=budget + 10.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases that already meet the Moore bound return at once.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: C annealing over voltage lifts with 1-3 base vertices per side.
    # Group orders are chosen just above the current best order.
    while time.monotonic() < deadline and best_n < lib.moore_bound(d, D):
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        m, k2, r = grp
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        budget = min(remaining, 2.0 + 2.0 * rng.random())
        try:
            n, e = _run_group(d, D, k, m, k2, r, rng.randrange(1, 2 ** 31), budget)
        except (RuntimeError, ValueError):
            continue
        if n > 0:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

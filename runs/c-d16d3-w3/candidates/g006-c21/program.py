"""Diameter-3 search by difference covers, with structured fallbacks.

Main idea: for an abelian group G of order m and a set S of d elements, the Haar graph
H(G, S) (vertex a in A is joined to vertex b in B iff b - a is in S) is bipartite and
d-regular on 2m vertices. It has diameter at most 3 exactly when S - S covers every
nonzero element of G. Since |S - S| <= d(d-1) + 1, this allows m up to d^2 - d + 1
(the Moore bound 2(d^2-d+1) is reached only by planes of order d-1).

The C engine searches for such covers by simulated annealing over Z_m and Z_a x Z_b,
for m in a range just below the bound, and reports the largest m it covers. Python builds
the graph, checks it with lib.is_valid, and keeps the best of the structured starts
(projective plane, Araujo-Pardo/Lopez, conic blow-up, W(q)) and K_{d,d}.
"""
import itertools
import time

import lib

C_HAAR = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 512
#define MAXK 64

static int M, N1, N2, K;
static int subt[MAXM * MAXM];
static int S[MAXK], inS[MAXM], cnt[MAXM], cost;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Group Z_n1 x Z_n2, element x*n2+y. subt[a*M+b] = a - b. */
static void setup_group(int n1, int n2) {
    N1 = n1;
    N2 = n2;
    M = n1 * n2;
    for (int a = 0; a < M; a++) {
        int a1 = a / N2, a2 = a % N2;
        for (int b = 0; b < M; b++) {
            int b1 = b / N2, b2 = b % N2;
            subt[a * M + b] = ((a1 - b1 + N1) % N1) * N2 + (a2 - b2 + N2) % N2;
        }
    }
}

/* cnt[r] = number of ordered pairs (i != j) with S_i - S_j = r; cost = #{r != 0 : cnt[r] == 0}. */
static void cinc(int r) {
    if (!r) return;
    if (cnt[r]++ == 0) cost--;
}
static void cdec(int r) {
    if (!r) return;
    if (--cnt[r] == 0) cost++;
}

static void remove_slot(int i) {
    int s = S[i];
    for (int j = 0; j < K; j++)
        if (j != i) {
            cdec(subt[s * M + S[j]]);
            cdec(subt[S[j] * M + s]);
        }
}

static void insert_slot(int i, int x) {
    for (int j = 0; j < K; j++)
        if (j != i) {
            cinc(subt[x * M + S[j]]);
            cinc(subt[S[j] * M + x]);
        }
    S[i] = x;
}

static void full_recount(void) {
    memset(cnt, 0, sizeof(cnt));
    cost = M - 1;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cinc(subt[S[i] * M + S[j]]);
}

/* One annealing run from a random K-subset. Returns 1 when S - S covers Z_M \ {0}. */
static int attempt(double until, long iters) {
    for (int i = 0; i < M; i++) inS[i] = 0;
    for (int i = 0; i < K; i++) {
        int x;
        do x = rndint(M);
        while (inS[x]);
        inS[x] = 1;
        S[i] = x;
    }
    full_recount();
    if (cost == 0) return 1;
    const double T0 = 1.5, T1 = 0.05;
    for (long it = 0; it < iters; it++) {
        if ((it & 255) == 0 && now() > until) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = rndint(K);
        int x = rndint(M);
        if (inS[x]) continue;
        int old = S[i];
        int c0 = cost;
        remove_slot(i);
        insert_slot(i, x);
        int delta = cost - c0;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[x] = 1;
            if (cost == 0) return 1;
        } else {
            remove_slot(i);
            insert_slot(i, old);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double end = t0 + budget;
    K = d;
    if (D != 3 || d < 2 || K > MAXK) {
        printf("0 0 0\n");
        return 0;
    }
    int hi = d * d - d + 1;
    if (hi > MAXM - 1) hi = MAXM - 1;
    int lo = (hi * 3) / 4;
    if (lo < d + 1) lo = d + 1;
    if (hi < lo) {
        printf("0 0 0\n");
        return 0;
    }

    int bestm = 0, bn1 = 0, bn2 = 0;
    int bS[MAXK];
    int count = hi - lo + 1;
    double slice = budget / (double)count;

    for (int m = lo; m <= hi && now() < end; m++) {
        int g1[32], g2[32], ng = 0;
        g1[ng] = m;
        g2[ng] = 1;
        ng++;
        for (int n2 = 2; n2 * n2 <= m; n2++) {
            if (m % n2) continue;
            int n1 = m / n2;
            if (n1 % n2 == 0 && ng < 32) {
                g1[ng] = n1;
                g2[ng] = n2;
                ng++;
            }
        }
        double mend = now() + slice;
        if (mend > end) mend = end;
        int found = 0;
        for (int gi = 0; gi < ng && !found; gi++) {
            double gend = now() + (mend - now()) / (double)(ng - gi);
            setup_group(g1[gi], g2[gi]);
            while (now() < gend) {
                if (attempt(gend, 400000L)) {
                    found = 1;
                    break;
                }
            }
            if (found) {
                bestm = m;
                bn1 = g1[gi];
                bn2 = g2[gi];
                memcpy(bS, S, sizeof(int) * (size_t)K);
            }
        }
    }

    if (bestm == 0) {
        printf("0 0 0\n");
        return 0;
    }
    printf("%d %d %d\n", bn1, bn2, K);
    for (int i = 0; i < K; i++) printf("%d ", bS[i]);
    printf("\n");
    return 0;
}
'''


def parse_cover(text):
    """Return (n1, n2, S) from the C output, or None when no cover was found."""
    nums = [int(x) for x in text.split()]
    if len(nums) < 3:
        return None
    n1, n2, k = nums[0], nums[1], nums[2]
    S = nums[3:3 + k]
    if n1 <= 0 or n2 <= 0 or k <= 0 or len(S) != k or len(set(S)) != k:
        return None
    return n1, n2, S


def haar_from_cover(n1, n2, S):
    """Haar graph of Z_n1 x Z_n2 with connection set S: a joined to a + s, on 2*m vertices."""
    m = n1 * n2
    edges = []
    for a in range(m):
        a1, a2 = divmod(a, n2)
        for s in S:
            s1, s2 = divmod(s, n2)
            b = ((a1 + s1) % n1) * n2 + (a2 + s2) % n2
            edges.append((a, m + b))
    return 2 * m, edges


def known_start(d, D):
    """Projective plane or Araujo-Pardo/Lopez graph for D = 3, when applicable."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def _gq_w(q):
    """Incidence graph of the generalized quadrangle W(q) (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def static_starts(d, D):
    """Structured starts; each is validated by the caller."""
    out = []
    if D == 3:
        ks = known_start(d, D)
        if ks is not None:
            out.append(ks)
        cb = conic_blowup(d, D)
        if cb is not None:
            out.append(cb)
    if D == 4 and d - 1 >= 2:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 75% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for every D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(g):
        nonlocal best
        try:
            if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = (g[0], list(g[1]))
        except Exception:
            pass

    try:
        for g in static_starts(d, D):
            consider(g)
    except Exception:
        pass

    if D == 3 and d >= 2:
        budget = 0.72 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 1.0:
            try:
                text = lib.run_c(C_HAAR, [d, D, seed, f"{budget:.2f}"], timeout=budget + 5.0)
                cov = parse_cover(text)
                if cov is not None:
                    consider(haar_from_cover(*cov))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

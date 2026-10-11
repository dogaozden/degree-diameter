"""Diameter-3 bipartite search: Haar graphs over small groups from a difference-cover search.

For a group G with a k-subset S, the Haar-type bipartite graph has parts A and B, each a copy of G,
with a_x adjacent to b_{x s} for s in S. It is k-regular with 2|G| vertices. It has diameter 3 exactly
when S S^-1 = G and S^-1 S = G. Vertices of A are then all within distance 2 of each other, and every
a-to-b distance is at most 3. So the search is a difference-cover problem: find the largest |G| <= k^2-k+1
with such an S. The C engine does simulated annealing over S for each candidate group (cyclic and
Z_m x|_r Z_k) and reports the largest order it can cover. A second family is the arc-extended projective
plane. K_{d,d} is the safe fallback. Python re-checks every result with lib.is_valid.
"""
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

#define MAXG 256
#define MAXK 64
#define MAXCAND 4096

typedef struct { int m, k, r; } Cand;

static int G, K;
static int MT[MAXG][MAXG];
static int IV[MAXG];
static int S[MAXK], inS[MAXG];
static int c1[MAXG], c2[MAXG];
static int cost;
static Cand cand[MAXCAND];
static int ncand;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gpow_mod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Multiplication table of Z_m x|_r Z_k, element (a,b) coded a*k+b, same as lib.semidirect_group. */
static void build_group(int m, int k, int r) {
    int pw[MAXK];
    for (int b = 0; b < k; b++) pw[b] = gpow_mod(r, b, m);
    G = m * k;
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        IV[x] = (int)(((m - ((long)pw[nb] * a) % m) % m) * k + nb);
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            MT[x][y] = (int)((((long)a + (long)pw[b] * c) % m) * k + (b + d) % k);
        }
    }
}

static void addc(int *c, int g) {
    if (g == 0) return;
    if (c[g]++ == 0) cost--;
}

static void remc(int *c, int g) {
    if (g == 0) return;
    if (--c[g] == 0) cost++;
}

/* Add (sgn > 0) or remove (sgn < 0) the two ordered pairs of distinct elements x, t. */
static void pair_op(int x, int t, int sgn) {
    int g1a = MT[x][IV[t]], g1b = MT[t][IV[x]];
    int g2a = MT[IV[x]][t], g2b = MT[IV[t]][x];
    if (sgn > 0) {
        addc(c1, g1a); addc(c1, g1b);
        addc(c2, g2a); addc(c2, g2b);
    } else {
        remc(c1, g1a); remc(c1, g1b);
        remc(c2, g2a); remc(c2, g2b);
    }
}

/* Replace S[i] by y (y not in S). */
static void swap_elem(int i, int y) {
    int x = S[i];
    for (int j = 0; j < K; j++)
        if (j != i) pair_op(x, S[j], -1);
    for (int j = 0; j < K; j++)
        if (j != i) pair_op(y, S[j], +1);
    S[i] = y;
    inS[x] = 0;
    inS[y] = 1;
}

/* Simulated annealing on the uncovered count of S S^-1 and S^-1 S. Returns 1 on success. */
static int attempt(double budget) {
    memset(inS, 0, sizeof(int) * G);
    memset(c1, 0, sizeof(int) * G);
    memset(c2, 0, sizeof(int) * G);
    cost = 2 * (G - 1);
    for (int i = 0; i < K; i++) {
        int y;
        do {
            y = (int)(rnd() % (uint64_t)G);
        } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) pair_op(S[i], S[j], +1);

    double t0 = now();
    double T = 1.0, fr = 0.0;
    long it = 0;
    while (cost > 0) {
        if ((it & 1023) == 0) {
            fr = (now() - t0) / budget;
            if (fr >= 1.0) break;
            T = 1.5 * (1.0 - fr) + 0.08 * fr;
        }
        it++;
        int i = (int)(rnd() % (uint64_t)K);
        int y;
        do {
            y = (int)(rnd() % (uint64_t)G);
        } while (inS[y]);
        int x = S[i];
        int before = cost;
        swap_elem(i, y);
        int delta = cost - before;
        if (delta > 0 && urand() >= exp(-(double)delta / T)) swap_elem(i, x);
    }
    return cost == 0;
}

/* Candidate groups of order N: cyclic, and semidirect Z_m x|_r Z_k with k <= 6. */
static void gen_cands(int N) {
    ncand = 0;
    for (int k = 1; k <= 6; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m < 2) continue;
        if (k == 1) {
            cand[ncand].m = m; cand[ncand].k = 1; cand[ncand].r = 1; ncand++;
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_int(r, m) != 1) continue;
            if (gpow_mod(r, k, m) != 1 % m) continue;
            if (ncand < MAXCAND) {
                cand[ncand].m = m; cand[ncand].k = k; cand[ncand].r = r; ncand++;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    K = atoi(argv[1]);
    int lo = atoi(argv[2]), hi = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    if (K < 1 || K > MAXK) {
        printf("0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1234567ULL;
    if (rs == 0) rs = 1;
    if (hi > MAXG - 1) hi = MAXG - 1;
    if (lo < K) lo = K;

    double t_end = now() + budget;
    int bestN = 0, bm = 0, bk = 0, br = 0;
    int bestS[MAXK];

    for (int N = lo; N <= hi; N++) {
        if (now() >= t_end) break;
        if (N < K) continue;
        gen_cands(N);
        if (ncand == 0) continue;
        for (int i = ncand - 1; i > 0; i--) {
            int j = (int)(rnd() % (uint64_t)(i + 1));
            Cand tmp = cand[i];
            cand[i] = cand[j];
            cand[j] = tmp;
        }
        int ok = 0;
        int tries = ncand < 4 ? ncand : 4;
        for (int c = 0; c < tries && !ok; c++) {
            double rem = t_end - now();
            if (rem < 0.02) break;
            double slice = rem * 0.3;
            build_group(cand[c].m, cand[c].k, cand[c].r);
            ok = attempt(slice);
            if (ok) {
                bestN = N;
                bm = cand[c].m;
                bk = cand[c].k;
                br = cand[c].r;
                memcpy(bestS, S, sizeof(int) * K);
            }
        }
        if (!ok) break;
    }

    if (bestN == 0) {
        printf("0\n");
        return 0;
    }
    printf("%d %d %d\n", bm, bk, br);
    for (int i = 0; i < K; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), a cheap second family.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Haar-type graphs over groups from the C difference-cover search.
# ----------------------------------------------------------------------------

def _haar_search(d, seed, budget):
    """Run the C search; return (n, edges) for the largest group found, or None."""
    lo, hi = d, min(d * d - d + 1, 250)
    text = lib.run_c(C_SOURCE, [d, lo, hi, seed, f"{budget:.2f}"], timeout=budget + 5.0)
    tok = text.split()
    if len(tok) < 3 + d or tok[0] == "0":
        return None
    m, k, r = int(tok[0]), int(tok[1]), int(tok[2])
    S = [int(x) for x in tok[3:3 + d]]
    order, mul, _inv = lib.semidirect_group(m, k, r)
    if len(set(S)) != d or any(not 0 <= s < order for s in S):
        return None
    edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
    return 2 * order, edges


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 72% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = (1, [])
    pool = [lib.haar_graph(d, range(d))]
    if D >= 3:
        pool += _arc_extensions(d, t0 + 0.15 * time_limit, rng)
    for n, e in pool:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3 and d >= 2:
        remaining = 0.72 * time_limit - (time.monotonic() - t0)
        if remaining > 1.0:
            try:
                g = _haar_search(d, seed, remaining)
            except Exception:
                g = None
            if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
    return best

"""Cyclic Haar graphs from difference covers (D = 3), with arc-extended PG(2,q) as fallback.

For D = 3 the main search is a C engine that looks for k-subsets S of Z_m whose
nonzero differences cover Z_m. Then H(m, S) (2m vertices, k-regular) has diameter 3.
The search climbs m upward from k+1 and keeps the largest m it certifies.
Other D use the arc-extended projective plane graphs (valid for D >= 3) or K_{d,d}.
"""
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd(int n) { return (int)(nxt() % (uint64_t)n); }
static double rnd01(void) { return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0); }

/* Replace S[i] by y. cnt[x] = number of ordered pairs (s,t), s != t, with s - t = x mod m.
   U = number of x in 1..m-1 with cnt[x] == 0. Both are kept exact. */
static void change(int *S, int k, int m, int *cnt, int *U, int i, int y) {
    int old = S[i];
    for (int j = 0; j < k; j++) {
        if (j == i) continue;
        int t = S[j];
        int a = (old - t + m) % m, b = (t - old + m) % m;
        if (--cnt[a] == 0) (*U)++;
        if (--cnt[b] == 0) (*U)++;
    }
    S[i] = y;
    for (int j = 0; j < k; j++) {
        if (j == i) continue;
        int t = S[j];
        int a = (y - t + m) % m, b = (t - y + m) % m;
        if (cnt[a]++ == 0) (*U)--;
        if (cnt[b]++ == 0) (*U)--;
    }
}

/* Simulated annealing for a difference cover of size k in Z_m. Returns 1 and fills Sout on success. */
static int try_cover(int k, int m, long iters, clock_t end, int *Sout) {
    int *S = malloc(sizeof(int) * k);
    int *cnt = calloc(m, sizeof(int));
    char *inS = calloc(m, 1);
    for (int i = 0; i < k; i++) {
        int y;
        do { y = rnd(m); } while (inS[y]);
        inS[y] = 1;
        S[i] = y;
    }
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            if (i != j) cnt[(S[i] - S[j] + m) % m]++;
    int U = 0;
    for (int x = 1; x < m; x++)
        if (cnt[x] == 0) U++;
    int ok = (U == 0);
    for (long it = 0; !ok && it < iters; it++) {
        if ((it & 4095) == 0 && clock() > end) break;
        double T = 0.35 * (1.0 - (double)it / (double)iters) + 0.03;
        int i = rnd(k), y = rnd(m);
        if (inS[y]) continue;
        int old = S[i];
        int oldU = U;
        change(S, k, m, cnt, &U, i, y);
        int dl = U - oldU;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            inS[old] = 0;
            inS[y] = 1;
            if (U == 0) ok = 1;
        } else {
            change(S, k, m, cnt, &U, i, old);
        }
    }
    if (ok) memcpy(Sout, S, sizeof(int) * k);
    free(S);
    free(cnt);
    free(inS);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) nxt();
    clock_t end = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);
    if (D != 3 || d < 2) { printf("0 0\n"); return 0; }
    int k = d;
    long cap = (long)k * (k - 1) + 1;
    int best = 0;
    int *bestS = malloc(sizeof(int) * k);
    int *tmp = malloc(sizeof(int) * k);
    long m = k + 1;
    while (m <= cap && clock() < end) {
        if (try_cover(k, (int)m, 1500000L, end, tmp)) {
            best = (int)m;
            memcpy(bestS, tmp, sizeof(int) * k);
            m++;
        }
    }
    if (best == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * best, best * k);
    for (int i = 0; i < best; i++)
        for (int j = 0; j < k; j++)
            printf("%d %d\n", i, best + (i + bestS[j]) % best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2,q) incidence (every vertex has degree q+1). With spare
# capacity s = d - q - 1, pick a point set S whose lines and points carry at
# most s members each. Add one new A-vertex per P in S (joined to lines through P)
# and one new B-vertex per j in S (joined to points on line j).
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
    """Return (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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
        arcs = _arc_extensions(d, t0 + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D == 3 and d >= 2:
        left = 0.80 * time_limit - (time.monotonic() - t0)
        if left > 2:
            try:
                txt = lib.run_c(C_SOURCE, [d, D, seed, round(left - 1.5, 2)],
                                stdin_graph=None, timeout=left + 2)
                n, e = lib.parse_graph_text(txt)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

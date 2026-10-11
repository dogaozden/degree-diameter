"""Bold variant: cyclic Haar graphs from difference covers.

For D = 3, the Haar graph of Z_m with connection set S (|S| = d) has diameter 3 exactly when
S - S covers Z_m. Then S + S - S = Z_m too, so the cross pairs are also within distance 3.
Such a graph has 2m vertices, which can beat projective-plane-based records. A C annealer
searches for the covering set S. Projective-plane and arc-extended constructions stay as the
safe fallback, and every candidate is checked with lib.is_valid before it is accepted.
"""
import random
import time

import lib

DIFF_SOURCE = r'''
/* Search for S in Z_M, |S| = K, with S - S covering every nonzero residue.
 * Usage: prog M K seed time_limit
 * Output: "OK M K s_1 ... s_K" or "FAIL". Simulated annealing on the uncovered count.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static uint64_t st = 88172645463325252ULL;
static uint64_t rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int M, K;
static int S[MAXK], inS[MAXM], cnt[MAXM];

static int md(int x) { x %= M; return x < 0 ? x + M : x; }

/* Replace element s = S[skip] by t. Returns the change in the number of uncovered
 * nonzero residues. The other members are S[j] for j != skip. Calling swapc(t, s, skip)
 * afterwards undoes the move. */
static int swapc(int s, int t, int skip) {
    int dc = 0;
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        int x = S[j];
        int a = md(s - x), b = md(x - s);
        if (--cnt[a] == 0) dc++;
        if (--cnt[b] == 0) dc++;
    }
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        int x = S[j];
        int a = md(t - x), b = md(x - t);
        if (cnt[a] == 0) dc--;
        cnt[a]++;
        if (cnt[b] == 0) dc--;
        cnt[b]++;
    }
    return dc;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (M < 2 || M > MAXM || K < 2 || K > MAXK || K > M || (long)M - 1 > (long)K * (K - 1)) {
        printf("FAIL\n");
        return 0;
    }
    st ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!st) st = 1;
    for (int i = 0; i < 10; i++) rnd();

    clock_t c0 = clock();
    long it = 0;
    double T = 1.0;
    for (;;) {
        memset(inS, 0, sizeof inS);
        memset(cnt, 0, sizeof cnt);
        S[0] = 0;             /* translation invariance: fix 0 in S */
        inS[0] = 1;
        for (int i = 1; i < K; i++) {
            int t;
            do t = rndint(M); while (inS[t]);
            S[i] = t;
            inS[t] = 1;
        }
        for (int i = 0; i < K; i++)
            for (int j = 0; j < K; j++)
                if (i != j) cnt[md(S[i] - S[j])]++;
        int cost = 0;
        for (int x = 1; x < M; x++)
            if (cnt[x] == 0) cost++;

        for (long run = 0; cost > 0 && run < 300000; run++) {
            it++;
            if ((it & 4095) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > limit) {
                printf("FAIL\n");
                return 0;
            }
            if ((run & 1023) == 0) T = pow(0.05, (double)run / 300000.0) + 0.02;
            int i = 1 + rndint(K - 1);
            int s = S[i];
            int t = rndint(M);
            if (inS[t]) continue;
            int dc = swapc(s, t, i);
            if (dc <= 0 || rnd01() < exp(-dc / T)) {
                cost += dc;
                inS[s] = 0;
                inS[t] = 1;
                S[i] = t;
            } else {
                swapc(t, s, i);
            }
        }
        if (cost == 0) {
            printf("OK %d %d", M, K);
            for (int i = 0; i < K; i++) printf(" %d", S[i]);
            printf("\n");
            return 0;
        }
    }
}
'''


def _pg_data(q):
    """Points/lines of PG(2, q): point i and line i share the vector pts[i]."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P. Diameter 3."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _cover_c(m, k, seconds, seed):
    """Ask the C annealer for k residues mod m whose differences cover Z_m. Returns S or None."""
    text = lib.run_c(DIFF_SOURCE, [m, k, seed, round(seconds, 2)], timeout=seconds + 5)
    tok = text.split()
    if len(tok) < 3 + k or tok[0] != "OK":
        return None
    S = [int(x) for x in tok[3:3 + k]]
    if len(set(S)) != k or any(not 0 <= x < m for x in S):
        return None
    diffs = {(a - b) % m for a in S for b in S if a != b}
    if diffs != set(range(1, m)):
        return None
    return S


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        # Stage 1: closed-form and arc-extended projective-plane constructions.
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.12 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

        # Stage 2 (bold): cyclic Haar graphs H(m, S) with |S| = d and S - S = Z_m.
        # These have 2m vertices, degree d, and diameter 3. Start just above the current best.
        end = t0 + 0.8 * time_limit
        m = best[0] // 2 + 1
        m_max = min(d * (d - 1) + 1, lib.moore_bound(d, D) // 2)
        while m <= m_max:
            remaining = end - time.monotonic()
            if remaining < 2.0:
                break
            secs = min(remaining - 1.0, max(3.0, 0.6 * remaining))
            try:
                S = _cover_c(m, d, secs, seed * 1000 + m)
            except RuntimeError:
                S = None
            if S is None:
                break
            n, edges = lib.haar_graph(m, S)
            consider((n, edges))
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

"""Diameter-3 search with a difference-cover construction (bi-Cayley / Haar-type graphs).

New construction: for a finite group G of order m and a set S of size d, the bipartite graph
with parts G x {A, B} and edges a_x -- b_{xs} (s in S) has degree d. It has diameter at most 3
iff S S^{-1} = G and S^{-1} S = G (A-A pairs need x^{-1}z in S S^{-1}, B-B pairs need
y^{-1}w in S^{-1} S, and A-B pairs are then within distance 3). Hence each side has at most
d(d-1)+1 vertices.

C engine: for each order m in [0.8(d^2-d+1), d^2-d+1], it tries semidirect products
Z_A x| Z_K (cyclic included) and anneals single-element swaps of S, with incremental coverage
counts of SS^{-1} and S^{-1}S. A zero-cost set gives a d-regular bipartite graph on 2m vertices,
which Python validates with lib.is_valid.

Other starts (projective-plane blow-ups and arc-extended PG(2,q) incidence graphs) stay in the
candidate pool. The largest valid graph wins, and K_{d,d} is always the fallback.
"""
import random
import time

import lib

C_DIFF = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 512
#define MAXK 64
#define MAXG 1024

static int K_, M_;
static int mt[MAXM][MAXM];
static int inv_[MAXM];
static int pw[MAXM];
static int S[MAXK];
static int present[MAXK];
static char inS[MAXM];
static int cL[MAXM], cR[MAXM];
static int covL, covR;
static uint64_t rs = 88172645463325252ULL;

typedef struct { int A, Kc, r; } Grp;
static Grp gl[MAXG];
static Grp bestG;
static int bestS[MAXK];
static int bestM = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Z_A x| Z_Kc with element (a,b) coded as a*Kc+b and (a,b)(c,e) = (a + r^b c, b+e). */
static void build_group(int A, int Kc, int r) {
    M_ = A * Kc;
    pw[0] = 1 % A;
    for (int b = 1; b < Kc; b++) pw[b] = (int)((long)pw[b - 1] * r % A);
    for (int x = 0; x < M_; x++) {
        int a = x / Kc, b = x % Kc;
        for (int y = 0; y < M_; y++) {
            int c = y / Kc, e = y % Kc;
            mt[x][y] = (int)(((a + (long)pw[b] * c) % A) * Kc + (b + e) % Kc);
        }
    }
    for (int x = 0; x < M_; x++)
        for (int y = 0; y < M_; y++)
            if (mt[x][y] == 0) { inv_[x] = y; break; }
}

static int enum_groups(int m, Grp *out, int maxout) {
    int cnt = 0;
    for (int A = m; A >= 2; A--) {
        if (m % A) continue;
        int Kc = m / A;
        for (int r = 1; r < A; r++) {
            if (gcd_i(r, A) != 1) continue;
            if (powmod(r, Kc, A) != 1 % A) continue;
            if (cnt < maxout) {
                out[cnt].A = A;
                out[cnt].Kc = Kc;
                out[cnt].r = r;
                cnt++;
            }
        }
    }
    return cnt;
}

static void bump(int *c, int *cov, int g, int delta) {
    if (delta > 0) {
        if (c[g] == 0) (*cov)++;
        c[g]++;
    } else {
        c[g]--;
        if (c[g] == 0) (*cov)--;
    }
}

/* Add (delta=+1) or remove (delta=-1) all ordered pairs involving element x at position self.
   Pairs are taken with the other present elements, plus the self pair. */
static void contrib(int x, int self, int delta) {
    int ix = inv_[x];
    bump(cL, &covL, mt[x][ix], delta);
    bump(cR, &covR, mt[ix][x], delta);
    for (int j = 0; j < K_; j++) {
        if (j == self || !present[j]) continue;
        int y = S[j], iy = inv_[y];
        bump(cL, &covL, mt[x][iy], delta);
        bump(cL, &covL, mt[y][ix], delta);
        bump(cR, &covR, mt[ix][y], delta);
        bump(cR, &covR, mt[iy][x], delta);
    }
}

static int cost(void) { return (M_ - covL) + (M_ - covR); }

static int reset_state(void) {
    memset(cL, 0, sizeof(int) * M_);
    memset(cR, 0, sizeof(int) * M_);
    covL = covR = 0;
    memset(inS, 0, sizeof(inS));
    for (int i = 0; i < K_; i++) {
        int x;
        do { x = rndint(M_); } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
        present[i] = 0;
    }
    for (int i = 0; i < K_; i++) {
        present[i] = 1;
        contrib(S[i], i, +1);
    }
    return cost();
}

/* Annealed single-swap search for S with SS^{-1} = G and S^{-1}S = G. Returns 1 on success. */
static int local_search(double until) {
    double T = 0.25 + 0.4 * rnd01();
    int cur = reset_state();
    int best = cur;
    long stall = 0;
    for (long it = 0;; it++) {
        if (cur == 0) return 1;
        if ((it & 1023) == 0 && now() > until) return 0;
        int i = rndint(K_);
        int old = S[i], nx;
        do { nx = rndint(M_); } while (inS[nx]);
        contrib(old, i, -1);
        inS[old] = 0;
        S[i] = nx;
        inS[nx] = 1;
        contrib(nx, i, +1);
        int nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            contrib(nx, i, -1);
            inS[nx] = 0;
            S[i] = old;
            inS[old] = 1;
            contrib(old, i, +1);
        }
        if (cur < best) {
            best = cur;
            stall = 0;
        } else if (++stall > 300000) {
            cur = reset_state();
            best = cur;
            stall = 0;
            T = 0.25 + 0.4 * rnd01();
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    K_ = d;
    if (D < 3 || K_ < 2 || K_ > MAXK) {
        printf("0 0\n");
        return 0;
    }
    int mhi = K_ * K_ - K_ + 1;
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    int mlo = (int)(0.8 * mhi);
    if (mlo < K_ + 1) mlo = K_ + 1;

    for (int m = mlo; m <= mhi; m++) {
        double remaining = t_end - now();
        if (remaining <= 0) break;
        double budget = remaining / (double)(mhi - m + 1);
        int ng = enum_groups(m, gl, MAXG);
        if (ng == 0) continue;
        /* keep the cyclic group at index 0, shuffle the rest */
        for (int a = ng - 1; a > 1; a--) {
            int b = 1 + rndint(a);
            Grp t = gl[a];
            gl[a] = gl[b];
            gl[b] = t;
        }
        int take = ng < 6 ? ng : 6;
        double per = budget / take;
        for (int g = 0; g < take; g++) {
            build_group(gl[g].A, gl[g].Kc, gl[g].r);
            if (local_search(now() + per)) {
                bestM = m;
                bestG = gl[g];
                memcpy(bestS, S, sizeof(int) * K_);
                break;
            }
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    build_group(bestG.A, bestG.Kc, bestG.r);
    int M = M_;
    printf("%d %d\n", 2 * M, M * K_);
    for (int i = 0; i < M; i++)
        for (int k = 0; k < K_; k++)
            printf("%d %d\n", i, M + mt[i][bestS[k]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (projective-plane based).
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Best directly constructible graph for D = 3: projective plane or Araujo-Pardo/Lopez."""
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def starts(d, D, deadline, rng):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 82% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.82 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    cands = []

    def consider(g):
        try:
            if g and lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass

    consider(lib.haar_graph(d, range(d)))  # K_{d,d}: always valid for D >= 2
    for g in starts(d, D, t0 + 0.12 * time_limit, rng):
        consider(g)

    # New engine: bi-Cayley graphs from difference covers over Z_A x| Z_K.
    if D >= 3 and d >= 2:
        budget = hard_end - time.monotonic() - 1.0
        if budget > 1.0:
            try:
                text = lib.run_c(C_DIFF, [d, D, seed, f"{budget:.2f}"],
                                 stdin_graph=None, timeout=budget + 5.0)
                n, e = lib.parse_graph_text(text)
                consider((n, e))
            except Exception:
                pass

    if not cands:
        return 1, []
    return max(cands, key=lambda g: g[0])

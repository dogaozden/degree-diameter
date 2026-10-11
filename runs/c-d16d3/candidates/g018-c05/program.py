"""Diameter-3 bipartite search with a difference-basis lift as the primary construction.

For D = 3, the Haar graph H(Z_m, S) with |S| = d has max degree d and diameter at most 3 whenever
the differences S - S cover every residue of Z_m. Since a-a pairs need a common neighbour, this
forces m <= d(d-1)+1, so the order is at most 2(d^2-d+1), which is the Moore bound. The C engine
searches for such a basis S by simulated annealing on the number of uncovered residues, and it
bisects on m. The Haar graph is valid by construction, and Python re-checks it with lib.is_valid.

The older arc-extended projective plane starts and the augmentation engine remain as fallbacks, and
they are still used for D >= 4. Every returned graph is validated, and K_{d,d} is the last resort.
"""
import itertools
import random
import time

import lib

DIFF_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 1200

static int d, M_;
static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];
static int U;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int md(int x) {
    x %= M_;
    if (x < 0) x += M_;
    return x;
}

/* Recompute counts of ordered differences and the number of uncovered nonzero residues. */
static void rebuild(void) {
    memset(inS, 0, sizeof(inS));
    memset(cnt, 0, sizeof(cnt));
    for (int i = 0; i < d; i++) inS[S[i]] = 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    U = 0;
    for (int r = 1; r < M_; r++)
        if (!cnt[r]) U++;
}

/* Replace S[i] by y, updating counts and U. Calling it again with the old value reverts. */
static void replace_at(int i, int y) {
    int x = S[i];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int r1 = md(x - S[j]);
        int r2 = md(S[j] - x);
        if (--cnt[r1] == 0) U++;
        if (--cnt[r2] == 0) U++;
    }
    inS[x] = 0;
    S[i] = y;
    inS[y] = 1;
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int r1 = md(y - S[j]);
        int r2 = md(S[j] - y);
        if (cnt[r1]++ == 0) U--;
        if (cnt[r2]++ == 0) U--;
    }
}

/* Simulated annealing for a difference basis of size d in Z_mm. Returns 1 and fills out on success. */
static int search(int mm, double deadline, int *out) {
    M_ = mm;
    memset(inS, 0, sizeof(inS));
    for (int i = 0; i < d; i++) {
        int y;
        do {
            y = rndint(M_);
        } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    rebuild();
    const long long E = 300000;
    long long step = 0;
    for (;;) {
        if (U == 0) {
            memcpy(out, S, sizeof(int) * (size_t)d);
            return 1;
        }
        if ((step & 4095) == 0 && now() > deadline) return 0;
        step++;
        double frac = (double)(step % E) / (double)E;
        double T = 1.2 * pow(0.03 / 1.2, frac);
        int i, y;
        if (rndint(2) == 0) {
            /* Focused move: cover a random uncovered residue r by y = S[j] +- r. */
            int off = rndint(M_), r = -1;
            for (int k = 0; k < M_; k++) {
                int c = (off + k) % M_;
                if (c != 0 && cnt[c] == 0) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
            int j = rndint(d);
            int sg = rndint(2) ? 1 : -1;
            y = md(S[j] + sg * r);
            if (inS[y]) continue;
            i = rndint(d - 1);
            if (i >= j) i++;
        } else {
            i = rndint(d);
            y = rndint(M_);
            if (inS[y]) continue;
        }
        int x = S[i];
        int oldU = U;
        replace_at(i, y);
        int delta = U - oldU;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) continue;
        replace_at(i, x);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 2 || d > MAXD || D != 3) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;

    double end = now() + budget;
    int ub = d * (d - 1) + 1;
    if (ub > MAXM - 1) ub = MAXM - 1;

    int lo = 0, hi = ub + 1, step = 4;
    int bestS[MAXD];
    int bestm = 0;

    while (now() < end) {
        int mid;
        if (lo == 0) {
            mid = hi - step;
        } else {
            if (hi - lo <= 1) break;
            mid = (lo + hi) / 2;
        }
        if (mid < d) mid = d;
        double remaining = end - now();
        if (remaining <= 0) break;
        double slice = budget * (lo == 0 ? 0.08 : 0.10);
        if (slice < 0.5) slice = 0.5;
        if (slice > remaining) slice = remaining;

        int tmp[MAXD];
        int ok;
        if (mid == d) {
            for (int i = 0; i < d; i++) tmp[i] = i;
            ok = 1;
        } else {
            ok = search(mid, now() + slice, tmp);
        }
        if (ok) {
            lo = mid;
            bestm = mid;
            memcpy(bestS, tmp, sizeof(int) * (size_t)d);
        } else {
            hi = mid;
            if (lo == 0) step *= 2;
        }
    }

    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    int m = bestm;
    printf("%d %d\n", 2 * m, m * d);
    for (int a = 0; a < m; a++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", a, m + (a + bestS[k]) % m);
    return 0;
}
"""


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of all vertices within distance r of src. */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* Try to add one new vertex on side X. Returns 1 if the graph grew. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, fallback starts).
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 13) + 1):
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
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# Drivers.
# ----------------------------------------------------------------------------

def _diff_basis_graph(d, seed, budget):
    """Run the difference-basis Haar search for D = 3 and return (n, edges)."""
    text = lib.run_c(DIFF_C, [d, 3, seed, f"{budget:.2f}"],
                     stdin_graph=None, timeout=budget + 10.0)
    return lib.parse_graph_text(text)


def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the augmentation C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else None

    # Primary construction for D = 3: Haar graph from a difference basis of Z_m.
    if D == 3 and d >= 2:
        try:
            n1, e1 = _diff_basis_graph(d, seed, 0.55 * time_limit)
            if lib.is_valid(n1, e1, d, D) and (best is None or n1 > best[0]):
                best = (n1, e1)
        except Exception:
            pass

    # Secondary starts: arc-extended projective planes (D >= 3), GQ (D >= 4).
    starts = []
    if D >= 3:
        try:
            starts.extend(_arc_extensions(d, time.monotonic() + 0.1 * time_limit, rng))
        except Exception:
            pass
    if D >= 4 and time.monotonic() < hard_end:
        try:
            gq = _best_gq(d)
            if gq is not None:
                starts.append(gq)
        except Exception:
            pass
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if best is not None:
        starts.append(best)
    if not starts:
        return best if best is not None else (1, [])
    starts.sort(key=lambda g: -g[0])
    best = starts[0]

    # Augment the top starts with the C engine, then keep augmenting the best result.
    plan = starts[:3]
    for idx in range(len(plan) + 1):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if idx < len(plan):
            src = plan[idx]
            share = remaining / (len(plan) + 1 - idx)
        else:
            src = best
            share = remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best

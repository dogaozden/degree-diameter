"""Diameter-3 bipartite search: difference-covering Haar graphs plus the arc-extended projective plane pipeline.

For D = 3, a Haar graph H(Z_m, S) with |S| = d is bipartite and d-regular. Its diameter is at most 3
exactly when the difference set S - S covers all of Z_m. A C simulated-annealing engine searches for
such covering sets S for increasing m and keeps the largest m it can cover. The result is verified with
lib.is_valid. The previous pipeline (arc-extended PG(2,q) starts with C augmentation) runs as a second
candidate, and the best valid graph is returned. K_{d,d} is the final safe fallback.
"""
import itertools
import random
import time

import lib

HAAR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static int K, M;
static int S[MAXK];
static int in[MAXM];
static int cnt[MAXM];
static int uncov;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int md(int a) {
    a %= M;
    if (a < 0) a += M;
    return a;
}

/* Maintain cnt[r] = number of ordered pairs (s,t), s != t, with s - t = r (mod M),
   and uncov = number of nonzero residues r with cnt[r] == 0. */
static void inc(int r, int sg) {
    if (sg > 0) {
        if (cnt[r] == 0) uncov--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) uncov++;
    }
}

/* Add (sg=+1) or remove (sg=-1) all ordered differences between slot i and every other slot. */
static void contrib(int i, int sg) {
    int x = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int y = S[j];
        inc(md(x - y), sg);
        inc(md(y - x), sg);
    }
}

static int search_m(int m, double deadline, int *out) {
    M = m;
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(in, 0, sizeof(int) * (size_t)M);
    uncov = M - 1;
    S[0] = 0;
    in[0] = 1;
    for (int i = 1; i < K; i++) {
        int v;
        do {
            v = 1 + (int)(rnd() % (uint64_t)(M - 1));
        } while (in[v]);
        S[i] = v;
        in[v] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            inc(md(S[i] - S[j]), 1);
            inc(md(S[j] - S[i]), 1);
        }
    if (uncov == 0) {
        for (int k = 0; k < K; k++) out[k] = S[k];
        return 1;
    }

    const double T0 = 1.0, T1 = 0.06;
    const long CYC = 300000;
    long it = 0;
    while (1) {
        if ((it & 1023) == 0 && now() >= deadline) break;
        it++;
        int i = 1 + (int)(rnd() % (uint64_t)(K - 1));
        int v;
        do {
            v = 1 + (int)(rnd() % (uint64_t)(M - 1));
        } while (in[v]);
        int old = uncov;
        int oldv = S[i];
        contrib(i, -1);
        in[oldv] = 0;
        S[i] = v;
        in[v] = 1;
        contrib(i, +1);
        int nw = uncov;
        if (nw > old) {
            double T = T0 * pow(T1 / T0, (double)(it % CYC) / (double)CYC);
            double u = (double)(rnd() % 1000000ULL) / 1000000.0;
            if (u >= exp(-(double)(nw - old) / T)) {
                contrib(i, -1);
                in[v] = 0;
                S[i] = oldv;
                in[oldv] = 1;
                contrib(i, +1);
            }
        }
        if (uncov == 0) {
            for (int k = 0; k < K; k++) out[k] = S[k];
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    K = atoi(argv[1]);
    int mlo = atoi(argv[2]);
    int mhi = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    if (K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    if (mlo < K + 1) mlo = K + 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;

    double t_end = now() + budget;
    double per = budget * 0.07;
    if (per < 0.2) per = 0.2;
    int best_m = 0;
    int bestS[MAXK], tmp[MAXK];
    int fails = 0;
    for (int m = mlo; m <= mhi; m++) {
        double t_now = now();
        if (t_now >= t_end) break;
        double cap = t_now + per;
        if (cap > t_end) cap = t_end;
        if (search_m(m, cap, tmp)) {
            best_m = m;
            memcpy(bestS, tmp, sizeof(int) * (size_t)K);
            fails = 0;
        } else if (++fails >= 3) {
            break;
        }
    }
    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_m, K);
    for (int k = 0; k < K; k++) printf("%d ", bestS[k]);
    printf("\n");
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
# Arc-extended projective plane incidence graphs (diameter 3).
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
# C drivers.
# ----------------------------------------------------------------------------

def _haar_search(d, seed, budget):
    """Search a difference-covering set S of size d in Z_m for the largest m; return the Haar graph or None."""
    text = lib.run_c(HAAR_SOURCE, [d, d + 1, d * (d - 1) + 1, seed, f"{budget:.2f}"],
                     timeout=budget + 10)
    nums = text.split()
    if len(nums) < 2:
        return None
    m, k = int(nums[0]), int(nums[1])
    if m <= 0 or k != d or len(nums) < 2 + k:
        return None
    S = [int(x) for x in nums[2:2 + k]]
    return lib.haar_graph(m, S)


def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the augmentation C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _legacy_build(d, D, seed, time_limit):
    """Arc-extended PG starts plus C augmentation; returns the best valid graph within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.25 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

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


def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found; K_{d,d} is the safe fallback."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = None

    def consider(g):
        nonlocal best
        if g is None:
            return
        try:
            if lib.is_valid(g[0], g[1], d, D) and (best is None or g[0] > best[0]):
                best = g
        except Exception:
            pass

    if D == 3 and d >= 2:
        # Bold path: difference-covering Haar graphs, which are d-regular with diameter 3.
        try:
            consider(_haar_search(d, seed, 0.42 * time_limit))
        except Exception:
            pass
        legacy_tl = 0.38 * time_limit
    else:
        legacy_tl = time_limit

    try:
        consider(_legacy_build(d, D, seed, legacy_tl))
    except Exception:
        pass

    if best is None:
        consider(lib.haar_graph(d, range(d)))
    if best is None:
        return 1, []
    return best

import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: search for a difference cover in a group of order G = M*J, where
# the group is the semidirect product Z_M x|_R Z_J (R = 1 gives a direct product).
#
# Let S be a K-subset of G and let H(S) be the bipartite graph on A = G and
# B = G with a_g ~ b_{g s} for s in S. It is K-regular. Then
#   A-A distance <= 2  iff  S S^{-1} = G,
#   B-B distance <= 2  iff  S^{-1} S = G,
#   A-B distance <= 3  follows from S S^{-1} = G.
# So H(S) has diameter 3 when both covers hold. The left action of G on itself
# preserves the graph, so checking BFS from a_e and b_e certifies the diameter.
# The annealer minimises the number of uncovered non-identity elements of
# S S^{-1} plus those of S^{-1} S. Nonabelian groups are a new source of
# candidates: they admit covers at orders where cyclic groups fail.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXK 64

static int K, M, J, R, G;
static int pw[MAXG];
static int mulT[MAXG][MAXG];
static int invT[MAXG];
static int cntL[MAXG];
static int cntR[MAXG];
static int zerosL, zerosR;
static int S[MAXK];
static int inS[MAXG];
static uint64_t rs = 88172645463325252ULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(nextr() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / J, b = x % J, c = y / J, d = y % J;
    return ((a + pw[b] * c) % M) * J + (b + d) % J;
}

static int ginv(int x) {
    int a = x / J, b = x % J;
    int nb = (J - b) % J;
    int na = (M - (pw[nb] * a) % M) % M;
    return na * J + nb;
}

static void bump(int *cnt, int x, int delta, int *zeros) {
    if (delta > 0) {
        if (cnt[x] == 0) (*zeros)--;
        cnt[x]++;
    } else {
        cnt[x]--;
        if (cnt[x] == 0) (*zeros)++;
    }
}

/* Add (delta=+1) or remove (delta=-1) the unordered pair {e,t} of distinct elements. */
static void pair_op(int e, int t, int delta) {
    bump(cntL, mulT[e][invT[t]], delta, &zerosL);
    bump(cntL, mulT[t][invT[e]], delta, &zerosL);
    bump(cntR, mulT[invT[t]][e], delta, &zerosR);
    bump(cntR, mulT[invT[e]][t], delta, &zerosR);
}

static void init_state(void) {
    int i, j;
    memset(cntL, 0, sizeof(cntL));
    memset(cntR, 0, sizeof(cntR));
    memset(inS, 0, sizeof(inS));
    zerosL = G - 1;
    zerosR = G - 1;
    for (i = 0; i < K; i++) inS[S[i]] = 1;
    for (i = 0; i < K; i++)
        for (j = i + 1; j < K; j++)
            pair_op(S[i], S[j], 1);
}

static void random_set(void) {
    int i, j, y, ok;
    for (i = 0; i < K; i++) {
        do {
            y = rndint(G);
            ok = 1;
            for (j = 0; j < i; j++)
                if (S[j] == y) ok = 0;
        } while (!ok);
        S[i] = y;
    }
}

static int anneal(double tl, clock_t t0) {
    long long it = 0;
    double T, frac, el;
    int cur, dl, nw, i, j, y, old;
    random_set();
    init_state();
    cur = zerosL + zerosR;
    while (cur > 0) {
        if ((it & 4095) == 0) {
            el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) return 0;
        }
        it++;
        frac = (double)(it % 300000) / 300000.0;
        T = 0.9 * pow(0.04 / 0.9, frac);
        i = rndint(K);
        y = rndint(G);
        if (inS[y]) continue;
        old = S[i];
        for (j = 0; j < K; j++)
            if (j != i) pair_op(old, S[j], -1);
        for (j = 0; j < K; j++)
            if (j != i) pair_op(y, S[j], 1);
        nw = zerosL + zerosR;
        dl = nw - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            S[i] = y;
            inS[old] = 0;
            inS[y] = 1;
            cur = nw;
        } else {
            for (j = 0; j < K; j++)
                if (j != i) pair_op(y, S[j], -1);
            for (j = 0; j < K; j++)
                if (j != i) pair_op(old, S[j], 1);
        }
    }
    return 1;
}

static int verify_print(void) {
    static int adj[2 * MAXG][MAXK];
    static int dist[2 * MAXG];
    static int queue[2 * MAXG];
    int N = 2 * G, g, k, src, si, qh, qt, v, u;
    for (g = 0; g < G; g++) {
        for (k = 0; k < K; k++) {
            adj[g][k] = G + mulT[g][S[k]];
            adj[G + g][k] = mulT[g][invT[S[k]]];
        }
    }
    for (si = 0; si < 2; si++) {
        src = (si == 0) ? 0 : G;
        for (v = 0; v < N; v++) dist[v] = -1;
        qh = 0;
        qt = 0;
        queue[qt++] = src;
        dist[src] = 0;
        while (qh < qt) {
            u = queue[qh++];
            for (k = 0; k < K; k++) {
                v = adj[u][k];
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    queue[qt++] = v;
                }
            }
        }
        if (qt != N) return 0;
        for (v = 0; v < N; v++)
            if (dist[v] > 3) return 0;
    }
    printf("%d %d\n", N, G * K);
    for (g = 0; g < G; g++)
        for (k = 0; k < K; k++)
            printf("%d %d\n", g, G + mulT[g][S[k]]);
    return 1;
}

int main(int argc, char **argv) {
    clock_t t0 = clock();
    double tl;
    unsigned long long seed;
    int i, x, y;
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    K = atoi(argv[1]);
    seed = strtoull(argv[3], NULL, 10);
    tl = atof(argv[4]);
    M = atoi(argv[5]);
    J = atoi(argv[6]);
    R = atoi(argv[7]);
    if (K < 2 || K > MAXK || M < 2 || J < 1 || (long long)M * J > MAXG) {
        printf("0 0\n");
        return 0;
    }
    G = M * J;
    if (K >= G || (long long)K * (K - 1) + 1 < G) {
        printf("0 0\n");
        return 0;
    }
    if (R < 1 || R >= M) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    pw[0] = 1 % M;
    for (i = 1; i < J; i++) pw[i] = (pw[i - 1] * R) % M;
    if ((pw[J - 1] * R) % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    for (x = 0; x < G; x++)
        for (y = 0; y < G; y++)
            mulT[x][y] = gmul(x, y);
    for (x = 0; x < G; x++)
        invT[x] = ginv(x);
    for (x = 0; x < G; x++)
        if (mulT[x][invT[x]] != 0) {
            printf("0 0\n");
            return 0;
        }
    if (!anneal(tl, t0)) {
        printf("0 0\n");
        return 0;
    }
    if (!verify_print())
        printf("0 0\n");
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
# Cyclic difference-cover Haar graphs (Python fallback, used only if the
# group search finds nothing).
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    """Return (cnt, zeros) for nonzero differences of S in Z_m."""
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    """Replace S[i] by y, updating cnt and the zero count. Returns the new zero count."""
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            a = (old - t) % m
            b = (t - old) % m
            cnt[a] -= 1
            if cnt[a] == 0:
                zeros += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            a = (y - t) % m
            b = (t - y) % m
            if cnt[a] == 0:
                zeros -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                zeros -= 1
            cnt[b] += 1
    return zeros


def _cover_search(k, m, deadline, rng):
    """Find a k-subset S of Z_m whose nonzero differences cover Z_m minus 0; return sorted S or None."""
    if k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    cnt, zeros = _diff_counts(S, m)
    T = 0.3
    moves = 0
    while zeros > 0:
        moves += 1
        if moves % 512 == 0 and time.monotonic() > deadline:
            return None
        if moves % 200000 == 0:
            S = rng.sample(range(m), k)
            cnt, zeros = _diff_counts(S, m)
            continue
        i = rng.randrange(k)
        y = rng.randrange(m)
        if y in S:
            continue
        old = S[i]
        z = _move(S, cnt, i, y, m, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _move(S, cnt, i, old, m, z)
    return sorted(S)


def _difference_graph(d, deadline, rng):
    """Largest cyclic Haar graph with |S| = d found before the deadline, as (n, edges), or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        S = _cover_search(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# NEW: difference-cover search over semidirect products (non-abelian groups).
#
# For a target order G, we try several groups Z_m x| Z_j (j * m = G, r^j = 1
# mod m). The C engine searches for a cover S of size d and prints the Haar
# graph H(S) with 2G vertices. A binary search over G finds the largest order
# for which some group succeeds within the budget.
# ----------------------------------------------------------------------------

GROUP_RUN_MAX_GROUPS = 4


def _group_candidates(G, rng):
    """Cyclic group first, then up to 3 semidirect products Z_m x| Z_j for each j | G (shuffled)."""
    out = []
    for j in range(2, 13):
        if G % j:
            continue
        m = G // j
        if m < 3:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, j, m) == 1 % m]
        rng.shuffle(rs)
        out += [(m, j, r) for r in rs[:3]]
    rng.shuffle(out)
    return [(G, 1, 1)] + out


def _group_cover_search(d, lo, deadline, seed, rng, per_run):
    """Binary search for the largest G with a group difference cover of size d; returns (n, edges) or None."""
    cap = d * (d - 1) + 1
    lo = max(lo, d + 1)
    hi = cap
    best = None

    def test(G):
        """Return a graph (success), False (all candidate groups failed), or None (out of time)."""
        idx = 0
        for (m, j, r) in _group_candidates(G, rng)[:GROUP_RUN_MAX_GROUPS]:
            left = deadline - time.monotonic()
            if left < 0.5:
                return None
            budget = min(per_run, left - 0.3)
            idx += 1
            sd = (seed * 1000003 + G * 1009 + idx) % (2 ** 31)
            try:
                txt = lib.run_c(C_SOURCE, [d, 3, sd, round(budget, 3), m, j, r], timeout=budget + 15)
                n, e = lib.parse_graph_text(txt)
            except (RuntimeError, ValueError):
                continue
            if n > 0 and lib.is_valid(n, e, d, 3):
                return (n, e)
        return False

    while lo < hi:
        mid = (lo + hi + 1) // 2
        res = test(mid)
        if res is None:
            break
        if res is False:
            hi = mid - 1
        else:
            best = res
            lo = mid
    return best


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates ("_augment").
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    per_run = max(0.5, min(1.5, 0.025 * time_limit))

    if D == 3:
        arcs = _arc_extensions(d, start + 0.06 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # Main search: difference covers in semidirect products, binary search on the order.
        g = _group_cover_search(d, best_n // 2, start + 0.80 * time_limit, seed, rng, per_run)
        if g is not None:
            consider(g[0], g[1])
        else:
            hg = _difference_graph(d, start + 0.90 * time_limit, rng)
            if hg is not None:
                consider(hg[0], hg[1])
    else:
        if D >= 3:
            arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:3]:
                consider(n_c, e_c)
            if arcs:
                n_a, e_a = arcs[0]
                n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.30 * time_limit)
                consider(n2, e2)

        if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        search_end = start + 0.55 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

        if D >= 2 and time.monotonic() < start + 0.85 * time_limit:
            n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
            consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

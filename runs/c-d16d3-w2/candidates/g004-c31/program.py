import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley voltage graphs over Z_m with block structure (diameter D).
#
# Vertices: A-blocks i = 0..K-1 and B-blocks j = 0..K-1, each block Z_m.
# a_i(x) ~ b_j(x + s) for every s in S_ij. Row sums and column sums of the
# block-count matrix N equal d, so every vertex has degree exactly d.
# Translation by Z_m is an automorphism, so the distance condition only needs
# BFS from one representative per block (2K BFS runs). Simulated annealing
# swaps elements inside each S_ij to drive the number of unreached
# (representative, vertex) pairs to zero. K = 1 is the cyclic Haar graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXM 2048
#define MAXNV (2 * MAXK * MAXM)

static int d, D, K, M;
static int Nm[MAXK][MAXK];
static unsigned char inS[MAXK][MAXK][MAXM];
static unsigned char bestS[MAXK][MAXK][MAXM];
static int bestK = 0, bestM = 0, bestN = 0;
static int *adj, *deg, *vis, *queue;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double nowsec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void build(void) {
    int NV = 2 * K * M;
    for (int v = 0; v < NV; v++) deg[v] = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int s = 0; s < M; s++) {
                if (!inS[i][j][s]) continue;
                for (int x = 0; x < M; x++) {
                    int a = i * M + x;
                    int b = K * M + j * M + (x + s) % M;
                    if (deg[a] < d && deg[b] < d) {
                        adj[a * d + deg[a]] = b;
                        deg[a]++;
                        adj[b * d + deg[b]] = a;
                        deg[b]++;
                    }
                }
            }
}

static long cost(void) {
    int NV = 2 * K * M;
    long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = (r < K) ? r * M : K * M + (r - K) * M;
        stamp++;
        int head = 0, tail = 0;
        queue[tail++] = src;
        vis[src] = stamp;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                int u = queue[head];
                for (int t = 0; t < deg[u]; t++) {
                    int v = adj[u * d + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        queue[tail++] = v;
                    }
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

static void randinit(void) {
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) {
            memset(inS[i][j], 0, (size_t)M);
            int c = 0;
            while (c < Nm[i][j]) {
                int s = rndint(M);
                if (!inS[i][j][s]) {
                    inS[i][j][s] = 1;
                    c++;
                }
            }
        }
}

static int anneal(double slice) {
    double t0 = nowsec(), tend = t0 + slice;
    int pi[MAXK * MAXK], pj[MAXK * MAXK], np = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (Nm[i][j] > 0 && Nm[i][j] < M) {
                pi[np] = i;
                pj[np] = j;
                np++;
            }
    randinit();
    build();
    long c = cost();
    if (np == 0) return c == 0;
    long it = 0;
    double T = 1.0;
    while (c > 0) {
        if ((it & 127) == 0) {
            double now = nowsec();
            if (now > tend) return 0;
            double f = (now - t0) / slice;
            T = pow(0.03, f);
        }
        it++;
        int q = rndint(np);
        int i = pi[q], j = pj[q];
        int s, t;
        do { s = rndint(M); } while (!inS[i][j][s]);
        do { t = rndint(M); } while (inS[i][j][t]);
        inS[i][j][s] = 0;
        inS[i][j][t] = 1;
        build();
        long c2 = cost();
        long delta = c2 - c;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            c = c2;
        } else {
            inS[i][j][s] = 1;
            inS[i][j][t] = 0;
            build();
        }
    }
    return 1;
}

static void setN(int k, int a) {
    K = k;
    if (a < 0) {
        int q = d / k, r = d % k;
        for (int i = 0; i < k; i++)
            for (int j = 0; j < k; j++)
                Nm[i][j] = q + (((j - i + k) % k) < r ? 1 : 0);
    } else {
        Nm[0][0] = a;
        Nm[0][1] = d - a;
        Nm[1][0] = d - a;
        Nm[1][1] = a;
    }
}

static void save_best(void) {
    bestK = K;
    bestM = M;
    memcpy(bestS, inS, sizeof(inS));
    bestN = 2 * K * M;
}

static void output(void) {
    if (bestN == 0) {
        printf("0 0\n");
        return;
    }
    int k = bestK, m = bestM;
    long E = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            for (int s = 0; s < m; s++)
                if (bestS[i][j][s]) E += m;
    printf("%d %ld\n", 2 * k * m, E);
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            for (int s = 0; s < m; s++) {
                if (!bestS[i][j][s]) continue;
                for (int x = 0; x < m; x++)
                    printf("%d %d\n", i * m + x, k * m + j * m + (x + s) % m);
            }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    adj = calloc((size_t)MAXNV * (size_t)d, sizeof(int));
    deg = calloc(MAXNV, sizeof(int));
    vis = calloc(MAXNV, sizeof(int));
    queue = calloc(MAXNV, sizeof(int));
    if (!adj || !deg || !vis || !queue) {
        printf("0 0\n");
        return 0;
    }

    int ck[24], ca[24], nc = 0;
    int base_k[] = {2, 1, 3, 4, 5, 6, 8};
    for (int t = 0; t < 7; t++)
        if (base_k[t] <= d && base_k[t] <= MAXK) {
            ck[nc] = base_k[t];
            ca[nc] = -1;
            nc++;
        }
    if (d >= 4) {
        int a1 = d / 2 - 2, a2 = d / 2 + 2;
        if (a1 >= 1 && a1 <= d - 1) {
            ck[nc] = 2;
            ca[nc] = a1;
            nc++;
        }
        if (a2 >= 1 && a2 <= d - 1) {
            ck[nc] = 2;
            ca[nc] = a2;
            nc++;
        }
    }

    double T_end = nowsec() + tl;
    for (int c = 0; c < nc; c++) {
        double now = nowsec();
        if (now >= T_end) break;
        double cfgEnd = now + (T_end - now) / (double)(nc - c);
        setN(ck[c], ca[c]);
        int maxN = 0;
        for (int i = 0; i < K; i++)
            for (int j = 0; j < K; j++)
                if (Nm[i][j] > maxN) maxN = Nm[i][j];
        int m0 = (d * d - d + 1) / (4 * K);
        if (m0 < maxN) m0 = maxN;
        if (m0 < 2) m0 = 2;
        M = m0;
        int lastok = 0;
        int step = M / 40;
        if (step < 1) step = 1;
        while (nowsec() < cfgEnd) {
            if (M >= MAXM) break;
            double rem = cfgEnd - nowsec();
            double slice = 0.25 * rem;
            if (slice < 0.2) slice = 0.2;
            if (slice > rem) slice = rem;
            if (anneal(slice)) {
                lastok = M;
                if (2 * K * M > bestN) save_best();
                M += step;
            } else {
                if (step > 1 && lastok > 0) {
                    step = 1;
                    M = lastok + 1;
                } else {
                    break;
                }
            }
        }
    }
    output();
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


# ----------------------------------------------------------------------------
# Driver for the C block-voltage search (D = 3 target path).
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, budget, timeout):
    """Run the C engine for `budget` seconds of search; returns (n, edges). Raises on failure."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=None, timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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

    if D == 3:
        # Cheap projective-plane extensions first (these are valid and fast).
        arcs = _arc_extensions(d, start + 0.05 * T, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

        # Bold new search: block-voltage graphs over Z_m, run in C.
        budget = max(1.0, 0.62 * T)
        try:
            n_c, e_c = _c_search(d, D, seed, budget, timeout=0.85 * T)
            consider(n_c, e_c)
        except Exception:
            pass

        # Greedy augmentation on the current best graph, within the remaining time.
        if time.monotonic() < start + 0.90 * T:
            try:
                n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.92 * T)
                consider(n_f, e_f)
            except Exception:
                pass
    else:
        if D >= 3:
            arcs = _arc_extensions(d, start + 0.10 * T, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:3]:
                consider(n_c, e_c)
            if arcs:
                n_a, e_a = arcs[0]
                n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.30 * T)
                consider(n2, e2)

        if D >= 4 and time.monotonic() < start + 0.30 * T:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        search_end = start + 0.55 * T
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

        if D >= 2 and time.monotonic() < start + 0.85 * T:
            n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * T)
            consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

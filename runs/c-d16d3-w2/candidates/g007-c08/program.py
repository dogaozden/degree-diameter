import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine. Two modes share one source:
#   "cover" k m0 seed time : simulated annealing for a difference cover of Z_m
#                            by a k-set S (every nonzero residue is some s - t).
#                            Searches m upward and prints the largest m found.
#                            The cyclic Haar graph H(m, S) is then k-regular,
#                            bipartite, and has diameter 3.
#   otherwise d D seed time: simulated annealing on a bipartite graph with a fixed
#                            vertex set (cost = pairs at distance > D). Whenever the
#                            cost reaches 0 it saves the graph and appends a vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 1;
static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static void seed_rng(uint64_t seed) {
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
}
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

/* ============================ cover search ============================ */

#define CMAXK 64
#define CMAXM 1100

static int ck, cm;
static int cS[CMAXK];
static int inS[CMAXM];
static int cnt[CMAXM];
static int czeros;

static void cover_reset_counts(void) {
    for (int x = 0; x < cm; x++) cnt[x] = 0;
    for (int i = 0; i < ck; i++)
        for (int j = 0; j < ck; j++)
            if (i != j) cnt[(cS[i] - cS[j] + cm) % cm]++;
    czeros = 0;
    for (int x = 1; x < cm; x++) if (cnt[x] == 0) czeros++;
}

static void cover_random_set(void) {
    for (int x = 0; x < cm; x++) inS[x] = 0;
    for (int i = 0; i < ck; i++) {
        int y;
        do { y = rint_(cm); } while (inS[y]);
        inS[y] = 1;
        cS[i] = y;
    }
    cover_reset_counts();
}

/* Replace cS[i] by y, update difference counts and the zero count. */
static int cover_replace(int i, int y) {
    int old = cS[i];
    for (int j = 0; j < ck; j++) {
        if (j == i) continue;
        int t = cS[j];
        int a = (old - t + cm) % cm;
        int b = (t - old + cm) % cm;
        if (--cnt[a] == 0) czeros++;
        if (--cnt[b] == 0) czeros++;
    }
    cS[i] = y;
    for (int j = 0; j < ck; j++) {
        if (j == i) continue;
        int t = cS[j];
        int a = (y - t + cm) % cm;
        int b = (t - y + cm) % cm;
        if (cnt[a]++ == 0) czeros--;
        if (cnt[b]++ == 0) czeros--;
    }
    return czeros;
}

static int cover_search(int k, int m, double budget, int *out) {
    ck = k; cm = m;
    cover_random_set();
    clock_t t0 = clock();
    long it = 0;
    while (czeros > 0) {
        if ((it & 4095) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > budget) return 0;
        }
        it++;
        if ((it % 3000000) == 0) { cover_random_set(); continue; }
        double ph = (double)(it % 400000) / 400000.0;
        double T = 0.2 + 0.8 * (1.0 - ph) * (1.0 - ph);
        int i = rint_(k);
        int y = rint_(cm);
        if (inS[y]) continue;
        int old = cS[i];
        int z0 = czeros;
        int z = cover_replace(i, y);
        int delta = z - z0;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            inS[old] = 0; inS[y] = 1;
        } else {
            cover_replace(i, old);
        }
    }
    for (int i = 0; i < k; i++) out[i] = cS[i];
    return 1;
}

static int cover_main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int k = atoi(argv[2]);
    int m = atoi(argv[3]);
    seed_rng((uint64_t)strtoull(argv[4], NULL, 10));
    double tl = atof(argv[5]);
    int cap = k * (k - 1) + 1;
    if (k < 2 || k > CMAXK || cap >= CMAXM) { printf("0 0\n"); return 0; }
    if (m > cap) m = cap;
    if (m < k + 1) m = k + 1;
    clock_t t0 = clock();
    int bestm = 0, fails = 0;
    int bestS[CMAXK], S[CMAXK];
    for (;;) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        double rem = tl - el;
        if (rem < 0.05) break;
        double slice = rem * 0.3;
        if (slice < 0.5) slice = rem;
        if (cover_search(k, m, slice, S)) {
            bestm = m;
            memcpy(bestS, S, sizeof(int) * (size_t)k);
            fails = 0;
            if (m >= cap) break;
            m++;
        } else {
            fails++;
            if (bestm == 0) {
                m--;
                if (m < k + 1) break;
            } else if (fails >= 3) {
                break;
            }
        }
    }
    if (bestm == 0) { printf("0 0\n"); return 0; }
    for (int i = 0; i < k; i++)
        for (int j = i + 1; j < k; j++)
            if (bestS[j] < bestS[i]) { int t = bestS[i]; bestS[i] = bestS[j]; bestS[j] = t; }
    printf("%d %d\n", bestm, k);
    for (int i = 0; i < k; i++) printf("%d\n", bestS[i]);
    return 0;
}

/* ============================ graph engine ============================ */

#define MAXN 1600
#define MAXW 25
#define DCAP 64
#define MAXE (MAXN * DCAP)

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static int vis[MAXN];

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

static int bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (nb[u][i] > u && m < MAXE) {
                bestU[m] = u; bestV[m] = nb[u][i]; m++;
            }
        }
    }
    best_n = n; best_m = m;
}

static int color_graph(void) {
    static int queue[MAXN];
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* a -- b  becomes  a -- w, where w is on the same side as b. */
static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int w = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != b && side[c] == side[b] && deg[c] < d && !adjm[a][c]) { w = c; break; }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    *ua = a; *ub = b; *uw = w;
    return 1;
}

static int move_add(int *ua, int *ub) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *ua = x; *ub = y;
    return 1;
}

static int move_remove(int *ua, int *ub) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *ua = a; *ub = b;
    return 1;
}

static int engine_main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed_rng((uint64_t)strtoull(argv[3], NULL, 10));
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) return 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    int ok = (n >= 2 && n <= MAXN - 256 && d >= 1 && d <= DCAP && D >= 1);
    if (ok) {
        for (int i = 0; i < m0 && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
                deg[u] >= d || deg[v] >= d) {
                ok = 0;
            } else {
                add_edge(u, v);
            }
        }
    }
    if (ok) ok = color_graph();
    if (!ok) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }

    int cur_bad = bad_pairs();
    int have_best = 0;
    if (cur_bad == 0) { save_best(); have_best = 1; }

    long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur_bad == 0) {
            save_best();
            have_best = 1;
            if (n >= MAXN - 2) break;
            side[n] = n & 1;
            deg[n] = 0;
            n++;
            cur_bad = bad_pairs();
            continue;
        }

        double phase = (double)(it % 60000) / 60000.0;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int kind = 0, ua = 0, ub = 0, uw = 0, applied = 0;
        int r = rint_(100);
        if (r < 55) { kind = 0; applied = move_rewire(&ua, &ub, &uw); }
        else if (r < 90) { kind = 1; applied = move_add(&ua, &ub); }
        else { kind = 2; applied = move_remove(&ua, &ub); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur_bad = nbad;
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else { add_edge(ua, ub); }
        }
    }

    if (!have_best) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) return 1;
    if (strcmp(argv[1], "cover") == 0) return cover_main(argc, argv);
    return engine_main(argc, argv);
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
# Cyclic Haar graphs from difference covers (diameter 3, valid for any D >= 3).
# ----------------------------------------------------------------------------

def _cover_graph(d, budget, seed):
    """Run the C cover search for a size-d difference cover; return H(m, S) as (n, edges), or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    m0 = max(k + 1, int(0.75 * cap))
    out = lib.run_c(C_SOURCE, ["cover", k, m0, seed, round(budget, 2)], timeout=budget + 10)
    nums = out.split()
    if len(nums) < 2:
        return None
    m, kk = int(nums[0]), int(nums[1])
    if m < 3 or kk != k:
        return None
    S = [int(x) for x in nums[2:2 + kk]]
    if len(S) != kk:
        return None
    return lib.haar_graph(m, S)


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4).
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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    final = t0 + 0.85 * time_limit - 1.0

    if D >= 3:
        # 1. Arc-extended projective plane graphs (cheap, valid for D >= 3).
        try:
            arcs = _arc_extensions(d, t0 + 0.08 * time_limit, random.Random(seed * 7919 + d))
            for g in sorted(arcs, key=lambda t: -t[0])[:3]:
                consider(g)
        except Exception:
            pass

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
        except Exception:
            pass

    if D >= 3:
        # 2. Difference-cover Haar graph search in C (main new source of order).
        budget = t0 + 0.6 * time_limit - time.monotonic()
        if budget > 1.0:
            try:
                hg = _cover_graph(d, budget, seed)
                if hg is not None:
                    consider(hg)
            except Exception:
                pass

        # 3. Annealing engine: start from the best valid graph and try to add vertices.
        eb = final - time.monotonic() - 0.5
        if eb > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(eb, 2)],
                                stdin_graph=best, timeout=eb + 8)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])

import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex/edge augmentation that keeps diameter <= D.
#
# Input: a valid bipartite graph. Adding a vertex never increases distances,
# so old pairs stay within D. A new vertex x on side c is valid iff its
# neighbours (all on the opposite side) cover every old vertex within
# distance D-1 of some neighbour. Greedy set cover over those balls decides it.
# Extra edges between opposite-side vertices with spare degree are always safe.
# A random edge-removal walk (checked by a full diameter test) frees degree
# when no insertion is possible; the best graph seen is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW 64

static int n, nw, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double budget_end;

static unsigned char pct[65536];

static void init_pct(void) {
    pct[0] = 0;
    for (int i = 1; i < 65536; i++) pct[i] = (unsigned char)(pct[i >> 1] + (i & 1));
}

static int pc(uint64_t x) {
    return pct[x & 0xffff] + pct[(x >> 16) & 0xffff] + pct[(x >> 32) & 0xffff] + pct[(x >> 48) & 0xffff];
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static int out_of_time(void) {
    return (double)clock() / CLOCKS_PER_SEC > budget_end;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void rem_edge(int u, int v) {
    del_from(u, v);
    del_from(v, u);
}

static int stamp_arr[MAXN];
static int stamp_cur = 0;
static int qb[MAXN];
static int dst[MAXN];

/* BFS from src to depth r. If out != NULL, writes the reached set as a bitset (nw words). */
static int ball(int src, int r, uint64_t *out) {
    int head = 0, tail = 0;
    stamp_cur++;
    qb[tail++] = src;
    stamp_arr[src] = stamp_cur;
    dst[src] = 0;
    while (head < tail) {
        int u = qb[head++];
        if (dst[u] >= r) continue;
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (stamp_arr[v] != stamp_cur) {
                stamp_arr[v] = stamp_cur;
                dst[v] = dst[u] + 1;
                qb[tail++] = v;
            }
        }
    }
    if (out) {
        for (int w = 0; w < nw; w++) out[w] = 0;
        for (int i = 0; i < tail; i++) {
            int v = qb[i];
            out[v >> 6] |= 1ULL << (v & 63);
        }
    }
    return tail;
}

static int full_ok(void) {
    for (int s = 0; s < n; s++) {
        if (ball(s, D, NULL) != n) return 0;
    }
    return 1;
}

static int color_graph(void) {
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        qb[tail++] = s;
        while (head < tail) {
            int u = qb[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qb[tail++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Add edges between opposite-colour vertices with spare degree (always keeps validity). */
static void edge_fill(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) A[na++] = v;
            else B[nb++] = v;
        }
    }
    for (int i = na - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = A[i]; A[i] = A[j]; A[j] = t;
    }
    for (int i = nb - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = B[i]; B[i] = B[j]; B[j] = t;
    }
    for (int i = 0; i < na; i++) {
        int a = A[i];
        for (int j = 0; j < nb && deg[a] < d; j++) {
            int b = B[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static uint64_t reach[MAXN * MAXW];
static int cand[MAXN];
static int chosen[MAXD];
static uint64_t Ucov[MAXW];

/* Try to add one new vertex on side opposite to copp, adjacent only to copp-side vertices. */
static int try_insert(int copp) {
    if (n >= MAXN) return 0;
    int nc = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] == copp && deg[v] < d) cand[nc++] = v;
    }
    if (nc == 0) return 0;
    for (int k = 0; k < nc; k++) {
        ball(cand[k], D - 1, reach + (size_t)k * MAXW);
    }
    for (int w = 0; w < nw; w++) Ucov[w] = 0;
    for (int v = 0; v < n; v++) Ucov[v >> 6] |= 1ULL << (v & 63);

    static char taken[MAXN];
    for (int k = 0; k < nc; k++) taken[k] = 0;

    int nu = 0;
    while (nu < d) {
        int bk = -1, bg = 0, ties = 0;
        for (int k = 0; k < nc; k++) {
            if (taken[k]) continue;
            const uint64_t *r = reach + (size_t)k * MAXW;
            int g = 0;
            for (int w = 0; w < nw; w++) g += pc(r[w] & Ucov[w]);
            if (g > bg) {
                bg = g;
                bk = k;
                ties = 1;
            } else if (g == bg && g > 0) {
                ties++;
                if (rndi(ties) == 0) bk = k;
            }
        }
        if (bk < 0) break;
        taken[bk] = 1;
        chosen[nu++] = cand[bk];
        const uint64_t *r = reach + (size_t)bk * MAXW;
        for (int w = 0; w < nw; w++) Ucov[w] &= ~r[w];
    }
    for (int w = 0; w < nw; w++) {
        if (Ucov[w]) return 0;
    }
    int x = n;
    col[x] = 1 - copp;
    deg[x] = 0;
    n++;
    nw = (n + 63) >> 6;
    for (int i = 0; i < nu; i++) add_edge(x, chosen[i]);
    return 1;
}

static int bn;
static int bdeg[MAXN], bcol[MAXN];
static int badj[MAXN][MAXD];

static void save_state(void) {
    bn = n;
    memcpy(bdeg, deg, sizeof deg);
    memcpy(bcol, col, sizeof col);
    memcpy(badj, adj, sizeof adj);
}

static void load_state(void) {
    n = bn;
    nw = (n + 63) >> 6;
    memcpy(deg, bdeg, sizeof deg);
    memcpy(col, bcol, sizeof col);
    memcpy(adj, badj, sizeof adj);
}

/* Remove a few random edges, keeping only removals that keep the diameter valid. */
static void perturb(int k) {
    for (int t = 0; t < k; t++) {
        for (int tries = 0; tries < 20; tries++) {
            int u = rndi(n);
            if (deg[u] == 0) continue;
            int v = adj[u][rndi(deg[u])];
            rem_edge(u, v);
            if (full_ok()) break;
            add_edge(u, v);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    init_pct();
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 5; i++) rnd64();
    budget_end = (double)clock() / CLOCKS_PER_SEC + budget;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN || m0 < 0 || d < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    nw = (n + 63) >> 6;
    memset(deg, 0, sizeof deg);
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= d || deg[v] >= d || has_edge(u, v)) {
            ok = 0;
            break;
        }
        add_edge(u, v);
    }
    if (!ok || !color_graph() || !full_ok()) {
        printf("0 0\n");
        return 0;
    }

    save_state();
    int best_n = n;
    int stall = 0;
    int just_perturbed = 0;

    while (!out_of_time()) {
        if (!just_perturbed) edge_fill();
        just_perturbed = 0;
        int progress = 0;
        for (int t = 0; t < 24 && !out_of_time(); t++) {
            int c = rndi(2);
            if (try_insert(c)) {
                progress = 1;
                edge_fill();
            }
        }
        if (n > best_n) {
            best_n = n;
            save_state();
            stall = 0;
        } else {
            stall++;
        }
        if (!progress) {
            perturb(1 + rndi(3));
            just_perturbed = 1;
        }
        if (stall > 400) {
            load_state();
            stall = 0;
            perturb(2 + rndi(4));
            just_perturbed = 1;
        }
    }

    if (n > best_n) save_state();
    load_state();

    int m = 0;
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) m++;
    }
    printf("%d %d\n", n, m);
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            if (adj[v][i] > v) printf("%d %d\n", v, adj[v][i]);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so spare s = d - q - 1. A-side: a multiset of points, each gets a new vertex
# joined to the q+1 lines through it. B-side: a multiset of lines, each gets a
# new vertex joined to the q+1 points on it. Diameter stays 3 for any multisets.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets with every target hit <= s times; returns the largest seen."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D = 4).
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed * 7919 + d)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Stage 1: constructions.
    if D >= 3:
        try:
            for g in _arc_extensions(d, start + 0.25 * tl, rng):
                consider(g)
        except Exception:
            pass
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                consider(lib.araujo_lopez_graph(q))
            except Exception:
                pass

    if D >= 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        anneal_deadline = start + 0.4 * tl
        while time.monotonic() < anneal_deadline:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_deadline, iters=400)
            consider(res)

    # Stage 2: C augmentation from the best start graph.
    remaining = start + 0.9 * tl - time.monotonic()
    if remaining > 3.0:
        cb = max(0.5, remaining - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(cb, 2)],
                            stdin_graph=best, timeout=max(1.0, remaining))
            n2, e2 = lib.parse_graph_text(out)
            consider((n2, e2))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
# A-side: a set SA of points, each gets a new vertex joined to its q+1 lines.
# B-side: a set SB of lines, each gets a new vertex joined to its q+1 points.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the same load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# C engine: greedy cover insertion with random restarts, plus a remove-and-
# reinsert local search.
#
# Key fact (new in this version): a new vertex X on side s whose neighbours lie
# on side 1-s is within distance 2 of every side-s vertex exactly when its
# neighbourhood covers all side-s vertices. If every side-(1-s) vertex has a
# neighbour (true for every vertex here), then every side-(1-s) vertex is within
# distance 3 of X. Adding vertices never increases distances between old
# vertices, so insertion preserves diameter 3 with no global check. Removals
# can break validity, so those moves are checked with a full BFS.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define MAXDEG 64

typedef struct {
    int N;
    int col[MAXV];
    int deg[MAXV];
    int adj[MAXV][MAXDEG];
} State;

static State SA, SB, SBEST;
static int dmax, Dd, baseN;
static uint64_t rs = 88172645463325252ULL;
static int stamp_arr[MAXV];
static int stampc = 0;
static int qbuf[MAXV];
static int cov[MAXV], used_[MAXV];

static uint64_t nextr(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static double unitr(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}
static double now(void) {
    return (double)clock() / CLOCKS_PER_SEC;
}

static void copy_state(State *d, const State *s) {
    d->N = s->N;
    memcpy(d->col, s->col, sizeof(int) * s->N);
    memcpy(d->deg, s->deg, sizeof(int) * s->N);
    memcpy(d->adj, s->adj, sizeof(int) * MAXDEG * s->N);
}

/* Insert a new vertex on `side` adjacent to a greedy cover of all side-vertices. */
static int try_insert(State *s, int side, double noise) {
    int N = s->N;
    int uncovered = 0;
    for (int v = 0; v < N; v++) {
        cov[v] = 0; used_[v] = 0;
        if (s->col[v] == side) uncovered++;
    }
    if (uncovered == 0 || N >= MAXV - 1) return 0;
    int picked[MAXDEG];
    int pc = 0;
    while (uncovered > 0 && pc < dmax) {
        double bs = -1e300; int bc = -1;
        for (int c = 0; c < N; c++) {
            if (s->col[c] == side || used_[c] || s->deg[c] >= dmax) continue;
            int g = 0;
            for (int i = 0; i < s->deg[c]; i++)
                if (!cov[s->adj[c][i]]) g++;
            if (g == 0) continue;
            double sc = g + noise * unitr();
            if (sc > bs) { bs = sc; bc = c; }
        }
        if (bc < 0) break;
        used_[bc] = 1;
        picked[pc++] = bc;
        for (int i = 0; i < s->deg[bc]; i++) {
            int u = s->adj[bc][i];
            if (!cov[u]) { cov[u] = 1; uncovered--; }
        }
    }
    if (uncovered > 0 || pc == 0) return 0;
    int x = N;
    s->N = N + 1;
    s->col[x] = side;
    s->deg[x] = 0;
    for (int k = 0; k < pc; k++) {
        int c = picked[k];
        s->adj[x][s->deg[x]++] = c;
        s->adj[c][s->deg[c]++] = x;
    }
    return 1;
}

/* Delete vertex x (must be an added vertex); the last vertex is moved into slot x. */
static void remove_vertex(State *s, int x) {
    for (int i = 0; i < s->deg[x]; i++) {
        int u = s->adj[x][i];
        for (int j = 0; j < s->deg[u]; j++) {
            if (s->adj[u][j] == x) {
                s->adj[u][j] = s->adj[u][s->deg[u] - 1];
                s->deg[u]--;
                break;
            }
        }
    }
    int last = s->N - 1;
    if (x != last) {
        s->col[x] = s->col[last];
        s->deg[x] = s->deg[last];
        memcpy(s->adj[x], s->adj[last], sizeof(int) * s->deg[last]);
        for (int i = 0; i < s->deg[x]; i++) {
            int w = s->adj[x][i];
            for (int j = 0; j < s->deg[w]; j++) {
                if (s->adj[w][j] == last) { s->adj[w][j] = x; break; }
            }
        }
    }
    s->N = last;
}

static int reach_count(const State *s, int src) {
    int head = 0, tail = 0, dep = 0;
    stampc++;
    qbuf[tail++] = src;
    stamp_arr[src] = stampc;
    while (head < tail && dep < Dd) {
        int end = tail;
        while (head < end) {
            int u = qbuf[head++];
            for (int i = 0; i < s->deg[u]; i++) {
                int v = s->adj[u][i];
                if (stamp_arr[v] != stampc) {
                    stamp_arr[v] = stampc;
                    qbuf[tail++] = v;
                }
            }
        }
        dep++;
    }
    return tail;
}

static int valid_state(const State *s) {
    for (int v = 0; v < s->N; v++)
        if (reach_count(s, v) != s->N) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    Dd = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (dmax > MAXDEG) dmax = MAXDEG;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n >= MAXV - 2 || dmax < 1 || Dd < 3) {
        printf("0 0\n");
        return 0;
    }
    State *cur = &SA, *tmp = &SB;
    cur->N = n;
    for (int v = 0; v < n; v++) cur->deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            cur->deg[u] >= dmax || cur->deg[v] >= dmax) { ok = 0; break; }
        cur->adj[u][cur->deg[u]++] = v;
        cur->adj[v][cur->deg[v]++] = u;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) cur->col[v] = -1;
    for (int s0 = 0; s0 < n; s0++) {
        if (cur->col[s0] >= 0) continue;
        cur->col[s0] = 0;
        int head = 0, tail = 0;
        qbuf[tail++] = s0;
        while (head < tail) {
            int u = qbuf[head++];
            for (int i = 0; i < cur->deg[u]; i++) {
                int v = cur->adj[u][i];
                if (cur->col[v] < 0) {
                    cur->col[v] = 1 - cur->col[u];
                    qbuf[tail++] = v;
                }
            }
        }
    }

    baseN = n;
    copy_state(&SBEST, cur);

    while (now() < budget) {
        copy_state(tmp, cur);
        int removed = 0;
        if (cur->N > baseN && (nextr() % 3) == 0) {
            int x = baseN + (int)(nextr() % (uint64_t)(cur->N - baseN));
            remove_vertex(tmp, x);
            removed = 1;
        }
        double noise = 1.5 * unitr();
        int got = 0;
        for (;;) {
            if (tmp->N >= MAXV - 2) break;
            int s0 = (int)(nextr() & 1);
            if (try_insert(tmp, s0, noise)) { got++; continue; }
            if (try_insert(tmp, 1 - s0, noise)) { got++; continue; }
            break;
        }
        if (!removed && got == 0) continue;
        int accept = 1;
        if (tmp->N < cur->N) accept = (unitr() < 0.02);
        if (removed && !valid_state(tmp)) accept = 0;
        if (accept) {
            State *t = cur; cur = tmp; tmp = t;
            if (cur->N > SBEST.N) copy_state(&SBEST, cur);
        }
    }

    State *b = &SBEST;
    int M = 0;
    for (int v = 0; v < b->N; v++)
        for (int i = 0; i < b->deg[v]; i++)
            if (b->adj[v][i] > v) M++;
    printf("%d %d\n", b->N, M);
    for (int v = 0; v < b->N; v++)
        for (int i = 0; i < b->deg[v]; i++)
            if (b->adj[v][i] > v) printf("%d %d\n", v, b->adj[v][i]);
    return 0;
}
'''


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
# Driver.
# ----------------------------------------------------------------------------

def _pg_starts(d):
    """Prime powers q with q + 1 <= d (so PG(2, q) fits degree d), largest first, at most two."""
    return sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)[:2]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.85 * time_limit
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
        # Baseline: arc-extended projective plane graphs (valid for D >= 3).
        arc_deadline = t0 + 0.15 * total
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

        # New: C greedy cover insertion (with remove/reinsert moves) starting from
        # the bare projective plane incidence graphs. Every insertion keeps diameter <= 3.
        starts = _pg_starts(d)
        frac = 0.8 if D == 3 else 0.4
        for i, q in enumerate(starts):
            rem = t0 + total - time.monotonic()
            if rem < 2.0:
                break
            budget = frac * rem / (len(starts) - i)
            n0, e0 = lib.projective_plane_incidence(q)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed + 1000 * i, round(budget, 2)],
                                stdin_graph=(n0, e0), timeout=budget + 10.0)
                consider(*lib.parse_graph_text(out))
            except (RuntimeError, ValueError):
                pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

        rng = random.Random(seed)
        deadline = t0 + total
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

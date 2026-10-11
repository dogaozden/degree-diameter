import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: capacitated multiset packing by simulated annealing.
#
# Input (stdin, graph text): entries 0..nx-1, targets nx..n-1, edge (x, nx+t) when
# entry x uses target t. Args: nx S seed time_limit.
# Choose multiplicities cnt[x] >= 0 so every target t has sum of cnt[x] over the
# entries x containing t at most S, maximising the total. Output: total, then one
# entry index per line (repeats for multiplicity).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int nx, nt, S, size;
static int *estart, *elist, *tstart, *tlist;
static int *cnt, *load, *perm, *bestcnt, *savecnt, *saveload;

static int feasible(int x) {
    if (estart[x + 1] == estart[x]) return 0;
    for (int i = estart[x]; i < estart[x + 1]; i++)
        if (load[elist[i]] >= S) return 0;
    return 1;
}

static void add1(int x) {
    cnt[x]++;
    size++;
    for (int i = estart[x]; i < estart[x + 1]; i++) load[elist[i]]++;
}

static void rem1(int x) {
    cnt[x]--;
    size--;
    for (int i = estart[x]; i < estart[x + 1]; i++) load[elist[i]]--;
}

static void greedy_fill(void) {
    for (int i = nx - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i];
        perm[i] = perm[j];
        perm[j] = t;
    }
    for (int j = 0; j < nx; j++) {
        int x = perm[j];
        while (feasible(x)) add1(x);
    }
}

/* Add x (must have cnt[x] == 0), evicting random entries that block one of its targets. */
static void force_add(int x) {
    for (int i = estart[x]; i < estart[x + 1]; i++) {
        int t = elist[i];
        while (load[t] >= S) {
            int base = tstart[t], deg = tstart[t + 1] - tstart[t];
            if (deg == 0) break;
            int off = rndint(deg), done = 0;
            for (int j = 0; j < deg && !done; j++) {
                int y = tlist[base + (off + j) % deg];
                if (cnt[y] > 0) {
                    rem1(y);
                    done = 1;
                }
            }
            if (!done) break;
        }
    }
    add1(x);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    nx = atoi(argv[1]);
    S = atoi(argv[2]);
    uint64_t sd = (uint64_t)strtoull(argv[3], NULL, 10);
    rs ^= sd * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0\n"); return 0; }
    if (nx < 0) nx = 0;
    if (nx > n) nx = n;
    nt = n - nx;
    if (nx == 0) { printf("0\n"); return 0; }

    int *ea = malloc(sizeof(int) * (size_t)(m + 1));
    int *eb = malloc(sizeof(int) * (size_t)(m + 1));
    int me = 0;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a > b) { int t = a; a = b; b = t; }
        if (a >= 0 && a < nx && b >= nx && b < n) {
            ea[me] = a;
            eb[me] = b - nx;
            me++;
        }
    }

    estart = calloc(nx + 2, sizeof(int));
    tstart = calloc(nt + 2, sizeof(int));
    for (int i = 0; i < me; i++) {
        estart[ea[i] + 1]++;
        tstart[eb[i] + 1]++;
    }
    for (int x = 0; x < nx; x++) estart[x + 1] += estart[x];
    for (int t = 0; t < nt; t++) tstart[t + 1] += tstart[t];
    elist = malloc(sizeof(int) * (size_t)(me + 1));
    tlist = malloc(sizeof(int) * (size_t)(me + 1));
    int *ep = malloc(sizeof(int) * (size_t)(nx + 1));
    int *tp = malloc(sizeof(int) * (size_t)(nt + 1));
    memcpy(ep, estart, sizeof(int) * (size_t)nx);
    memcpy(tp, tstart, sizeof(int) * (size_t)nt);
    for (int i = 0; i < me; i++) {
        elist[ep[ea[i]]++] = eb[i];
        tlist[tp[eb[i]]++] = ea[i];
    }

    cnt = calloc(nx + 1, sizeof(int));
    load = calloc(nt + 1, sizeof(int));
    perm = malloc(sizeof(int) * (size_t)(nx + 1));
    bestcnt = calloc(nx + 1, sizeof(int));
    savecnt = calloc(nx + 1, sizeof(int));
    saveload = calloc(nt + 1, sizeof(int));
    for (int i = 0; i < nx; i++) perm[i] = i;

    int mind = 1 << 30;
    for (int x = 0; x < nx; x++) {
        int deg = estart[x + 1] - estart[x];
        if (deg > 0 && deg < mind) mind = deg;
    }
    long long ub = (mind < (1 << 30)) ? ((long long)S * nt) / mind : 0;

    size = 0;
    greedy_fill();
    int bestsize = size;
    memcpy(bestcnt, cnt, sizeof(int) * (size_t)nx);

    double T = 0.5;
    long long it = 0, lastimp = 0;
    clock_t c0 = clock();
    while ((long long)bestsize < ub) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;
        int x = rndint(nx);
        if (cnt[x] > 0 || estart[x + 1] == estart[x]) continue;
        int oldsize = size;
        memcpy(savecnt, cnt, sizeof(int) * (size_t)nx);
        memcpy(saveload, load, sizeof(int) * (size_t)nt);
        force_add(x);
        greedy_fill();
        int delta = size - oldsize;
        if (delta >= 0 || rnd01() < exp(delta / T)) {
            if (size > bestsize) {
                bestsize = size;
                memcpy(bestcnt, cnt, sizeof(int) * (size_t)nx);
                lastimp = it;
            }
        } else {
            memcpy(cnt, savecnt, sizeof(int) * (size_t)nx);
            memcpy(load, saveload, sizeof(int) * (size_t)nt);
            size = oldsize;
        }
        T *= 0.99997;
        if (T < 0.08) T = 0.08;
        if (it - lastimp > 300000) {
            T = 0.5;
            lastimp = it;
        }
    }

    printf("%d\n", bestsize);
    for (int x = 0; x < nx; x++)
        for (int c = 0; c < bestcnt[x]; c++) printf("%d\n", x);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: multiset SA of points. Each entry gets a new vertex joined to the q+1
#         lines through it. Each line may be hit by at most s entries.
# B-side: multiset SB of lines, symmetric.
#
# Diameter stays 3 for any such multisets (see the argument in _arc_graph notes),
# so the problem is pure capacitated packing: maximise |SA| (and |SB|) subject to
# per-target load <= s. The upper bound is s*m/(q+1) per side. The packing is
# solved by the C annealer above, with a Python fallback.
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
    """True if every target t is hit by <= s entries of S (repeats counted), where entry x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Python fallback: iterated greedy over multisets with per-target load <= s."""
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


def _pack_c(nbr, m, s, seed, budget):
    """Solve the capacitated packing with the C annealer. Returns a list of entry indices."""
    nx = len(nbr)
    edges = [(x, nx + t) for x, lst in enumerate(nbr) for t in lst]
    out = lib.run_c(C_SOURCE, [nx, s, seed, round(budget, 2)],
                    stdin_graph=(nx + m, edges), timeout=budget + 20)
    nums = out.split()
    k = int(nums[0])
    chosen = [int(v) for v in nums[1:1 + k]]
    if len(chosen) != k:
        raise ValueError("truncated packing output")
    return chosen


def _pack(nbr, m, s, seed, budget, rng):
    """Largest packing found: C annealer first, Python greedy fallback if anything goes wrong."""
    if s <= 0 or not nbr:
        return []
    try:
        ch = _pack_c(nbr, m, s, seed, max(0.5, budget))
        if _loads_ok(ch, s, m, nbr):
            return ch
    except Exception:
        pass
    return _multi_side(m, s, nbr, rng, time.monotonic() + min(max(budget, 0.2), 3.0))


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


def _arc_ub(d, q):
    """Upper bound on the order of the arc-extended graph for prime power q (per side s*m/(q+1))."""
    s = d - q - 1
    m = q * q + q + 1
    return 2 * m + 2 * ((s * m) // (q + 1))


def _arc_extensions(d, deadline, seed):
    """Return (n, edges) candidates for the most promising prime powers q with q + 1 <= d."""
    rng = random.Random(seed * 7919 + d)
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    qs.sort(key=lambda q: -_arc_ub(d, q))
    qs = qs[:4]
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _pack(point_lines, m, s, rng.randrange(1 << 30), per_side, rng)
        SB = _pack(line_points, m, s, rng.randrange(1 << 30), per_side, rng)
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
# Simulated annealing over bi-Cayley voltage lifts (for D >= 5 and as a D = 4 extra).
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

    # Arc-extended projective plane graphs, with the A and B multisets found by the
    # C capacitated-packing annealer. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        frac = 0.8 if D == 3 else 0.25
        cands = _arc_extensions(d, start + frac * time_limit, seed)
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        deadline = start + 0.7 * time_limit
        if time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # Main search: annealed group voltage lifts. For D >= 5 use larger bases.
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
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

import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

static int d, D, n, cap, W;
static int *deg, *col, *adjf, *candl, *chosen, *qbuf;
static u64 *bA, *bB, *bT, *cov;
static u64 rs = 88172645463325252ULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adjf[a * d + deg[a]] = b;
    deg[a]++;
    adjf[b * d + deg[b]] = a;
    deg[b]++;
}

static void del_half(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) if (adjf[a * d + i] == b) break;
    if (i < deg[a]) {
        adjf[a * d + i] = adjf[a * d + deg[a] - 1];
        deg[a]--;
    }
}

static void remove_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

/* out[v] = bitmask of vertices within distance r of v */
static void balls(int r, u64 *out) {
    int v, k, i, w;
    memset(out, 0, sizeof(u64) * (size_t)n * W);
    for (v = 0; v < n; v++) out[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (k = 0; k < r; k++) {
        for (v = 0; v < n; v++) {
            u64 *dst = bT + (size_t)v * W;
            memcpy(dst, out + (size_t)v * W, sizeof(u64) * W);
            for (i = 0; i < deg[v]; i++) {
                const u64 *src = out + (size_t)adjf[v * d + i] * W;
                for (w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        memcpy(out, bT, sizeof(u64) * (size_t)n * W);
    }
}

static int all_full(const u64 *b) {
    int v, w, fw = n / 64, rem = n % 64;
    for (v = 0; v < n; v++) {
        const u64 *row = b + (size_t)v * W;
        for (w = 0; w < fw; w++) if (row[w] != ~0ULL) return 0;
        if (rem) {
            u64 mk = (1ULL << rem) - 1;
            if ((row[fw] & mk) != mk) return 0;
        }
    }
    return 1;
}

/* Greedy cover of all n vertices by balls (radius D-1, stored in bA) of
   vertices with colour cc and spare degree. Returns number of picks or -1. */
static int cover_pick(int cc, int at, int *out) {
    int nc = 0, k, w, picks = 0, covered = 0, off = 0;
    for (k = 0; k < n; k++) if (col[k] == cc && deg[k] < d) candl[nc++] = k;
    if (nc == 0) return -1;
    for (w = 0; w < W; w++) cov[w] = 0;
    if (at > 0) off = (int)(rnd() % (u64)nc);
    while (covered < n && picks < d) {
        int best = -1, bestg = 0;
        for (k = 0; k < nc; k++) {
            int j = k + off, s, g = 0, ww;
            if (j >= nc) j -= nc;
            s = candl[j];
            {
                const u64 *bs = bA + (size_t)s * W;
                for (ww = 0; ww < W; ww++) g += pc(bs[ww] & ~cov[ww]);
            }
            if (g > bestg) { bestg = g; best = s; }
        }
        if (best < 0) return -1;
        out[picks++] = best;
        for (w = 0; w < W; w++) cov[w] |= bA[(size_t)best * W + w];
        covered += bestg;
    }
    return covered >= n ? picks : -1;
}

static void output(void) {
    int v, k, u, m = 0;
    for (v = 0; v < n; v++)
        for (k = 0; k < deg[v]; k++) if (adjf[v * d + k] > v) m++;
    printf("%d %d\n", n, m);
    for (v = 0; v < n; v++)
        for (k = 0; k < deg[v]; k++) {
            u = adjf[v * d + k];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    int m0, i, k, a, b, v, s, nc, cc, at, done, nc0, kk;
    int *eu, *ev;
    double budget;
    clock_t t0;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    t0 = clock();
    if (scanf("%d %d", &n, &m0) != 2 || n <= 0 || d < 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    eu = malloc(sizeof(int) * (m0 + 1));
    ev = malloc(sizeof(int) * (m0 + 1));
    for (i = 0; i < m0; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    cap = 2 * n + 64;
    W = (cap + 63) / 64;
    deg = calloc(cap, sizeof(int));
    col = calloc(cap, sizeof(int));
    adjf = calloc((size_t)cap * d, sizeof(int));
    candl = calloc(cap, sizeof(int));
    qbuf = calloc(cap, sizeof(int));
    chosen = calloc(d + 1, sizeof(int));
    bA = calloc((size_t)cap * W, sizeof(u64));
    bB = calloc((size_t)cap * W, sizeof(u64));
    bT = calloc((size_t)cap * W, sizeof(u64));
    cov = calloc(W, sizeof(u64));
    for (i = 0; i < m0; i++) {
        int x = eu[i], y = ev[i];
        if (x < 0 || x >= n || y < 0 || y >= n || x == y || deg[x] >= d || deg[y] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(x, y);
    }
    for (i = 0; i < n; i++) col[i] = -1;
    for (i = 0; i < n; i++) if (col[i] < 0) {
        int qh = 0, qt = 0;
        col[i] = 0;
        qbuf[qt++] = i;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (k = 0; k < deg[u]; k++) {
                int x = adjf[u * d + k];
                if (col[x] < 0) { col[x] = 1 - col[u]; qbuf[qt++] = x; }
            }
        }
    }
    balls(D, bB);
    if (!all_full(bB)) {
        output();
        return 0;
    }
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
        if (n + 1 >= cap) break;
        a = (int)(rnd() % (u64)n);
        if (deg[a] == 0) continue;
        b = adjf[a * d + (int)(rnd() % (u64)deg[a])];
        remove_edge(a, b);
        balls(D - 1, bA);
        done = 0;
        nc0 = (int)(rnd() & 1);
        for (s = 0; s < 2 && !done; s++) {
            nc = nc0 ^ s;
            cc = 1 - nc;
            for (at = 0; at < 3 && !done; at++) {
                kk = cover_pick(cc, at, chosen);
                if (kk < 0) continue;
                v = n;
                n++;
                col[v] = nc;
                deg[v] = 0;
                for (i = 0; i < kk; i++) add_edge(chosen[i], v);
                balls(D, bB);
                if (all_full(bB)) {
                    done = 1;
                } else {
                    for (i = 0; i < kk; i++) remove_edge(chosen[i], v);
                    n--;
                }
            }
        }
        if (!done) add_edge(a, b);
    }
    output();
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _twin_grow(n, edges, d, rng, deadline):
    """Add twins (same side, same neighbourhood) while neighbours have spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _remove_twins(n, edges, frac, rng):
    """Delete a random fraction of redundant twins; the diameter is preserved."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    classes = {}
    for v in range(n):
        if adj[v]:
            classes.setdefault(frozenset(adj[v]), []).append(v)
    cands = []
    for grp in classes.values():
        if len(grp) >= 2:
            cands.extend(grp[1:])
    if not cands:
        return n, list(edges)
    k = max(1, int(frac * len(cands)))
    drop = set(rng.sample(cands, min(k, len(cands))))
    keep = [v for v in range(n) if v not in drop]
    idx = {v: i for i, v in enumerate(keep)}
    new_e = [(idx[u], idx[v]) for u, v in edges if u not in drop and v not in drop]
    return len(keep), new_e


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover every vertex within distance D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(25):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices (only shortens distances)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        consider(*base)
    if best_n >= lib.moore_bound(d, D):
        return best

    seed_c = seed % 100003 + 1

    # Phase A: pipelines from the structured base.
    if base is not None:
        t_end = start + 0.30 * T
        cur = None
        while time.monotonic() < t_end:
            if cur is None or rng.random() < 0.3:
                sn, se = base
            else:
                sn, se = _remove_twins(cur[0], cur[1], 0.15, rng)
            pn, pe = _pipeline(sn, se, d, D, t_end, rng)
            consider(pn, pe)
            if cur is None or pn >= cur[0]:
                cur = (pn, pe)

    def c_phase(until, salt):
        """Run the C exchange engine from the current best graph until `until`."""
        sec = until - time.monotonic() - 1.0
        if sec < 1.0:
            return None
        try:
            txt = lib.run_c(C_SOURCE, [d, D, seed_c * 7 + salt, round(sec, 2)],
                            stdin_graph=best, timeout=sec + 20.0)
            return lib.parse_graph_text(txt)
        except Exception:
            return None

    def polish(until):
        """Use spare degree: saturate, grow twins and covers, saturate again."""
        pn, pe = best
        pe = _saturate_edges(pn, pe, d, rng)
        pn, pe = _pipeline(pn, pe, d, D, until, rng)
        return pn, _saturate_edges(pn, pe, d, rng)

    # Phase C1: C exchange search, then polish.
    res = c_phase(start + 0.55 * T, 1)
    if res is not None:
        consider(*res)
    pn, pe = polish(start + 0.64 * T)
    consider(pn, pe)

    # Phase C2: second C exchange run from the improved best, then polish.
    res = c_phase(start + 0.84 * T, 2)
    if res is not None:
        consider(*res)
    pn, pe = polish(start + 0.90 * T)
    consider(pn, pe)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

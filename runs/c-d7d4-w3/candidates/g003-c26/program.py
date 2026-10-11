import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int N, CAP, DEG, DIA, W, BN;
static int *gdeg, *gadj, *side;
static int *bdeg, *badj, *bside;
static u64 *bufA, *bufB, *cov;
static int *used, *cand, *gain, *chosen;
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd64() % (unsigned long long)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitmask per vertex of all vertices within distance r. Returns pointer to result buffer. */
static u64 *compute_ball(int r) {
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(u64) * (size_t)W);
            for (int k = 0; k < gdeg[v]; k++) {
                const u64 *nb = cur + (size_t)gadj[v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= nb[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIA (unreachable pairs count). */
static long long cost_now(void) {
    const u64 *B = compute_ball(DIA);
    long long c = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(B[(size_t)v * W + w]);
        c += N - pc;
    }
    return c / 2;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < gdeg[u]; k++)
        if (gadj[u * DEG + k] == v) return 1;
    return 0;
}
static void del_arc(int u, int v) {
    for (int k = 0; k < gdeg[u]; k++) {
        if (gadj[u * DEG + k] == v) {
            gadj[u * DEG + k] = gadj[u * DEG + gdeg[u] - 1];
            gdeg[u]--;
            return;
        }
    }
}
static void add_arc(int u, int v) { gadj[u * DEG + gdeg[u]] = v; gdeg[u]++; }
static void add_edge(int u, int v) { add_arc(u, v); add_arc(v, u); }
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Degree-preserving bipartite double-edge switch: (a,b),(c,e) -> (a,e),(c,b), a,c on side 0. */
static int do_switch(int *o) {
    for (int t = 0; t < 200; t++) {
        int a = rndint(N);
        if (side[a] != 0 || gdeg[a] == 0) continue;
        int b = gadj[a * DEG + rndint(gdeg[a])];
        int c = rndint(N);
        if (side[c] != 0 || c == a || gdeg[c] == 0) continue;
        int e = gadj[c * DEG + rndint(gdeg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        o[0] = a; o[1] = b; o[2] = c; o[3] = e;
        return 1;
    }
    return 0;
}

static void undo_switch(const int *o) {
    int a = o[0], b = o[1], c = o[2], e = o[3];
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Add edges between non-adjacent deficient opposite-side vertices. Never increases cost. */
static int saturate(void) {
    int *L = malloc(sizeof(int) * (size_t)(N + 1));
    int *R = malloc(sizeof(int) * (size_t)(N + 1));
    int nl = 0, nr = 0, added = 0;
    for (int v = 0; v < N; v++) {
        if (gdeg[v] < DEG) {
            if (side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && gdeg[a] < DEG; j++) {
            int b = R[j];
            if (gdeg[b] < DEG && !has_edge(a, b)) {
                add_edge(a, b);
                added++;
            }
        }
    }
    free(L);
    free(R);
    return added;
}

/* Add one vertex whose neighbours (<= DEG deficient opposite-side vertices) cover all
   vertices within distance DIA-1. Keeps validity. Returns 1 on success. */
static int try_grow(void) {
    if (DIA < 2 || N + 1 > CAP) return 0;
    const int full = N;
    const u64 *B = compute_ball(DIA - 1);
    for (int att = 0; att < 40; att++) {
        for (int st = 0; st < 2; st++) {
            int c = (st + att) & 1;
            int nc = 0;
            for (int u = 0; u < N; u++)
                if (side[u] == 1 - c && gdeg[u] < DEG) cand[nc++] = u;
            if (nc == 0) continue;
            memset(cov, 0, sizeof(u64) * (size_t)W);
            int k = 0, covcnt = 0;
            while (covcnt < full && k < DEG) {
                int best = 0;
                for (int i = 0; i < nc; i++) {
                    int u = cand[i];
                    int g = 0;
                    if (!used[u]) {
                        for (int w = 0; w < W; w++)
                            g += popc(B[(size_t)u * W + w] & ~cov[w]);
                    }
                    gain[i] = g;
                    if (g > best) best = g;
                }
                if (best == 0) break;
                int pick = -1;
                if (att == 0) {
                    for (int i = 0; i < nc; i++)
                        if (gain[i] == best) { pick = i; break; }
                } else {
                    int thr = best;
                    if (best > 1 && rndint(2) == 0) thr = best - 1;
                    int opts = 0;
                    for (int i = 0; i < nc; i++)
                        if (gain[i] >= thr && gain[i] > 0) opts++;
                    int r = rndint(opts);
                    for (int i = 0; i < nc; i++) {
                        if (gain[i] >= thr && gain[i] > 0) {
                            if (r == 0) { pick = i; break; }
                            r--;
                        }
                    }
                }
                int u = cand[pick];
                used[u] = 1;
                chosen[k++] = u;
                for (int w = 0; w < W; w++) cov[w] |= B[(size_t)u * W + w];
                covcnt = 0;
                for (int w = 0; w < W; w++) covcnt += popc(cov[w]);
            }
            for (int j = 0; j < k; j++) used[chosen[j]] = 0;
            if (covcnt == full && k > 0) {
                int v = N;
                N++;
                side[v] = c;
                gdeg[v] = 0;
                for (int j = 0; j < k; j++) add_edge(chosen[j], v);
                return 1;
            }
        }
    }
    return 0;
}

static void save_best(void) {
    BN = N;
    memset(bdeg, 0, sizeof(int) * (size_t)CAP);
    memcpy(bdeg, gdeg, sizeof(int) * (size_t)N);
    memcpy(badj, gadj, sizeof(int) * (size_t)N * DEG);
    memcpy(bside, side, sizeof(int) * (size_t)N);
}

static void restore_best(void) {
    N = BN;
    memset(gdeg, 0, sizeof(int) * (size_t)CAP);
    memcpy(gdeg, bdeg, sizeof(int) * (size_t)N);
    memcpy(gadj, badj, sizeof(int) * (size_t)N * DEG);
    memcpy(side, bside, sizeof(int) * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 5; i++) rnd64();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 <= 0 || DEG < 1 || DIA < 1 || m0 < 0) { printf("0 0\n"); return 0; }

    CAP = 2 * n0 + 64;
    W = (CAP + 63) / 64;
    gdeg = calloc((size_t)CAP, sizeof(int));
    gadj = calloc((size_t)CAP * DEG, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    bdeg = calloc((size_t)CAP, sizeof(int));
    badj = calloc((size_t)CAP * DEG, sizeof(int));
    bside = calloc((size_t)CAP, sizeof(int));
    bufA = calloc((size_t)CAP * W, sizeof(u64));
    bufB = calloc((size_t)CAP * W, sizeof(u64));
    cov = calloc((size_t)W, sizeof(u64));
    used = calloc((size_t)CAP, sizeof(int));
    cand = calloc((size_t)CAP, sizeof(int));
    gain = calloc((size_t)CAP, sizeof(int));
    chosen = calloc((size_t)DEG + 1, sizeof(int));

    N = n0;
    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { bad = 1; break; }
        if (gdeg[u] >= DEG || gdeg[v] >= DEG || has_edge(u, v)) { bad = 1; break; }
        add_edge(u, v);
    }
    if (bad) { printf("0 0\n"); return 0; }

    int *queue = malloc(sizeof(int) * (size_t)(n0 + 1));
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int k = 0; k < gdeg[x]; k++) {
                int y = gadj[x * DEG + k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    queue[qt++] = y;
                } else if (side[y] == side[x]) {
                    bad = 1;
                }
            }
        }
    }
    free(queue);
    if (bad) { printf("0 0\n"); return 0; }

    BN = 0;
    long long cur = cost_now();
    if (cur == 0) save_best();
    saturate();
    cur = cost_now();
    if (cur == 0 && N > BN) save_best();

    double T = 0.6;
    long long since = 0;
    int ops[4];
    while (now_sec() < budget) {
        if (cur == 0) {
            if (N > BN) save_best();
            if (try_grow()) {
                saturate();
                cur = cost_now();
                if (cur == 0 && N > BN) save_best();
            } else {
                for (int i = 0; i < 8; i++) do_switch(ops);
                cur = cost_now();
            }
            since = 0;
            T = 0.6;
            continue;
        }
        since++;
        if (BN > 0 && since > 4000) {
            restore_best();
            saturate();
            cur = cost_now();
            since = 0;
            T = 0.6;
            continue;
        }
        if (!do_switch(ops)) continue;
        long long nc = cost_now();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo_switch(ops);
        }
        T *= 0.9995;
        if (T < 0.05) T = 0.05;
    }

    if (BN <= 0) { printf("0 0\n"); return 0; }
    long long m = 0;
    for (int v = 0; v < BN; v++) m += bdeg[v];
    m /= 2;
    printf("%d %lld\n", BN, m);
    for (int v = 0; v < BN; v++) {
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[v * DEG + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """Dense structured graph of degree >= d, thinned later into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
            for attempt in range(200):
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
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


def _duplicate_twins(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Thinning a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad_cnt = [m - b.bit_count() for b in ball]
        if sum(bad_cnt) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad_cnt[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Voltage lifts over small (semidirect) groups, annealed to diameter <= D.
# ----------------------------------------------------------------------------

def _group_options(G):
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline):
    darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    temp = 0.6
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return n, e


def _lift_phase(d, D, get_best, deadline, rng, consider):
    while time.monotonic() < deadline:
        best_n = get_best()
        s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
        G_min = best_n // (2 * s) + 1
        G = G_min + rng.randrange(4)
        opts = _group_options(G)
        if not opts:
            continue
        M, k, r = rng.choice(opts)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res = _lift_search(d, D, s, G, mul, rng, slice_end)
        if res is not None:
            n, e = res
            consider(n, e)
            n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
            consider(n2, e2)


# ----------------------------------------------------------------------------
# C refinement: anneal and grow a valid graph in the C engine.
# ----------------------------------------------------------------------------

def _c_refine(d, D, n, e, seconds, seed, consider):
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}"],
                        stdin_graph=(n, e), timeout=seconds + 10.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return False
    return consider(n2, e2)


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.8 * time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, twin/grow trials   -> 0.20
#   B  thinned dense graph (degree reduction + vertex deletion)     -> 0.27
#   L  voltage lifts over small groups                              -> 0.35
#   C  C engine refinement from the best valid graph (two runs)     -> 0.60, 0.80
# Every kept graph passes lib.is_valid; the Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit

    def at(f):
        return start + f * budget

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown; then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.20)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense graph.
    if D >= 2 and time.monotonic() < at(0.27):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.27):
                r = _deletion_trial(d, D, rn, re, rng, at(0.27))
                if r is None:
                    break
                consider(*r)

    # Phase L: voltage lifts.
    if D >= 2 and time.monotonic() < at(0.35):
        _lift_phase(d, D, lambda: best_n, at(0.35), rng, consider)

    # Phase C: C engine from the best valid graph found so far.
    if D >= 2:
        for k, end in enumerate((0.60, 0.80)):
            if time.monotonic() > at(end) - 2.0:
                continue
            secs = at(end) - time.monotonic() - 1.0
            if secs < 1.0:
                continue
            _c_refine(d, D, best_n, best_e, secs,
                      (seed * 7919 + k) & 0xFFFFFFFF, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)

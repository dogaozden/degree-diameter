import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int d, D, cap, W, n;
static int *nb, *deg, *side, *bad;
static u64 *bufA, *bufB, *ballR, *covb;
static int *Lbuf, *Rbuf, *candbuf, *chosen;
static int best_n = 0, best_m = 0;
static int *snap_side, *snap_eu, *snap_ev;
static u64 rs = 1;
static double t_start = 0.0, t_budget = 0.0;
static double temp = 0.5;

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int m) { return (int)(rnd() % (u64)m); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = nb + (size_t)a * d;
    for (int k = 0; k < deg[a]; k++) if (p[k] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    int *p = nb + (size_t)a * d;
    for (int k = 0; k < deg[a]; k++) {
        if (p[k] == b) { p[k] = p[deg[a] - 1]; deg[a]--; return; }
    }
}

static void add_arc(int a, int b) {
    nb[(size_t)a * d + deg[a]] = b;
    deg[a]++;
}

static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

/* Bitsets of radius-r balls for the current n, written into out (stride Wn). */
static void compute_balls(int r, u64 *out) {
    int Wn = (n + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        u64 *p = cur + (size_t)v * Wn;
        memset(p, 0, sizeof(u64) * (size_t)Wn);
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * Wn;
            const u64 *src = cur + (size_t)v * Wn;
            memcpy(dst, src, sizeof(u64) * (size_t)Wn);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *su = cur + (size_t)nb[(size_t)v * d + k] * Wn;
                for (int w = 0; w < Wn; w++) dst[w] |= su[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    memcpy(out, cur, sizeof(u64) * (size_t)n * (size_t)Wn);
}

/* Number of unordered pairs at distance > D (unreachable counts). Fills bad[]. */
static int eval_cost(void) {
    int Wn = (n + 63) >> 6;
    compute_balls(D, ballR);
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        const u64 *p = ballR + (size_t)v * Wn;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += popc(p[w]);
        bad[v] = n - c;
        tot += n - c;
    }
    return (int)(tot / 2);
}

/* Add one vertex joined to a greedy cover of the other side. Returns 1 if added. */
static int grow_one(void) {
    if (n >= cap || n < 1) return 0;
    int Wn = (n + 63) >> 6;
    compute_balls(D - 1, ballR);
    int c = rint_(2);
    for (int w = 0; w < Wn; w++) covb[w] = 0;
    int nc = 0;
    for (int s = 0; s < n; s++)
        if (side[s] == 1 - c && deg[s] < d) candbuf[nc++] = s;
    int k = 0;
    while (k < d) {
        int bestg = 0, bestc = -1, ties = 0;
        for (int i = 0; i < nc; i++) {
            int s = candbuf[i];
            if (s < 0) continue;
            const u64 *bs = ballR + (size_t)s * Wn;
            int g = 0;
            for (int w = 0; w < Wn; w++) g += popc(bs[w] & ~covb[w]);
            if (g > bestg) { bestg = g; bestc = i; ties = 1; }
            else if (g == bestg && g > 0) {
                ties++;
                if (rint_(ties) == 0) bestc = i;
            }
        }
        if (bestc < 0) break;
        int s = candbuf[bestc];
        candbuf[bestc] = -1;
        chosen[k++] = s;
        const u64 *bs = ballR + (size_t)s * Wn;
        for (int w = 0; w < Wn; w++) covb[w] |= bs[w];
    }
    if (k == 0) return 0;
    int v = n;
    n++;
    side[v] = c;
    deg[v] = 0;
    for (int i = 0; i < k; i++) add_edge(chosen[i], v);
    return 1;
}

static void shuffle_arr(int *arr, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = arr[i]; arr[i] = arr[j]; arr[j] = t;
    }
}

/* Join deficient opposite-side vertices. Never increases the cost. */
static void fill_all(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) Lbuf[nl++] = v;
            else Rbuf[nr++] = v;
        }
    }
    shuffle_arr(Lbuf, nl);
    shuffle_arr(Rbuf, nr);
    for (int i = 0; i < nl; i++) {
        int a = Lbuf[i];
        for (int j = 0; j < nr; j++) {
            if (deg[a] >= d) break;
            int b = Rbuf[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void remove_vertex(int x) {
    while (deg[x] > 0) {
        int u = nb[(size_t)x * d + deg[x] - 1];
        del_edge(x, u);
    }
    int L = n - 1;
    if (x != L) {
        for (int k = 0; k < deg[L]; k++) {
            int w = nb[(size_t)L * d + k];
            int *p = nb + (size_t)w * d;
            for (int j = 0; j < deg[w]; j++) {
                if (p[j] == L) { p[j] = x; break; }
            }
        }
        memcpy(nb + (size_t)x * d, nb + (size_t)L * d, sizeof(int) * (size_t)d);
        deg[x] = deg[L];
        side[x] = side[L];
    }
    deg[L] = 0;
    n--;
}

static void snapshot(void) {
    best_n = n;
    best_m = 0;
    for (int v = 0; v < n; v++) snap_side[v] = side[v];
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[(size_t)v * d + k];
            if (v < u) {
                snap_eu[best_m] = v;
                snap_ev[best_m] = u;
                best_m++;
            }
        }
    }
}

static void load_snapshot(void) {
    n = best_n;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        side[v] = snap_side[v];
    }
    for (int i = 0; i < best_m; i++) add_edge(snap_eu[i], snap_ev[i]);
}

static int pick_swap(int *pa, int *pb, int *pc, int *pe) {
    if (n < 4) return 0;
    int a = rint_(n);
    if (deg[a] == 0) return 0;
    int b = nb[(size_t)a * d + rint_(deg[a])];
    int c = rint_(n);
    if (c == a || side[c] != side[a] || deg[c] == 0) return 0;
    int e = nb[(size_t)c * d + rint_(deg[c])];
    if (e == b) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}

static void do_swap(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_swap(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Restart from the best valid graph with a small random removal, then regrow one vertex more. */
static int restart_state(void) {
    if (best_n > 0) {
        load_snapshot();
        int k = rint_(3);
        for (int i = 0; i < k; i++) {
            int x = rint_(n);
            remove_vertex(x);
        }
        fill_all();
        for (int i = 0; i <= k; i++) {
            if (grow_one()) fill_all();
        }
    }
    static const double temps[4] = {0.2, 0.35, 0.5, 0.8};
    temp = temps[rint_(4)];
    return eval_cost();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    t_budget = atof(argv[4]);
    t_start = wall();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 1 || m0 < 0 || d < 2 || D < 2) { printf("0 0\n"); return 0; }

    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { printf("0 0\n"); return 0; }
        if (iu[i] < 0 || iu[i] >= n0 || iv[i] < 0 || iv[i] >= n0 || iu[i] == iv[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    double s = 0.0, p = 1.0;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (double)(d - 1);
        if (s > 1e9) break;
    }
    double moore = 2.0 * s;
    long long lim = (long long)moore + 2;
    if (lim < (long long)n0 + 2) lim = (long long)n0 + 2;
    long long soft = (long long)n0 + 200;
    if (soft < 3000) soft = 3000;
    if (lim > soft) lim = soft;
    cap = (int)lim;
    W = (cap + 63) >> 6;

    nb = malloc(sizeof(int) * (size_t)cap * (size_t)d);
    deg = calloc((size_t)cap, sizeof(int));
    side = calloc((size_t)cap, sizeof(int));
    bad = calloc((size_t)cap, sizeof(int));
    bufA = calloc((size_t)cap * (size_t)W, sizeof(u64));
    bufB = calloc((size_t)cap * (size_t)W, sizeof(u64));
    ballR = calloc((size_t)cap * (size_t)W, sizeof(u64));
    covb = calloc((size_t)W + 1, sizeof(u64));
    Lbuf = malloc(sizeof(int) * (size_t)cap);
    Rbuf = malloc(sizeof(int) * (size_t)cap);
    candbuf = malloc(sizeof(int) * (size_t)cap);
    chosen = malloc(sizeof(int) * (size_t)(d + 1));
    snap_side = calloc((size_t)cap, sizeof(int));
    snap_eu = malloc(sizeof(int) * (size_t)cap * (size_t)d);
    snap_ev = malloc(sizeof(int) * (size_t)cap * (size_t)d);

    n = n0;
    for (int i = 0; i < m0; i++) {
        int a = iu[i], b = iv[i];
        if (deg[a] >= d || deg[b] >= d || has_edge(a, b)) { printf("0 0\n"); return 0; }
        add_edge(a, b);
    }

    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s0 = 0; s0 < n; s0++) {
        if (side[s0] != -1) continue;
        side[s0] = 0;
        int qh = 0, qt = 0;
        Rbuf[qt++] = s0;
        while (qh < qt) {
            int v = Rbuf[qh++];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[(size_t)v * d + k];
                if (side[u] == -1) {
                    side[u] = 1 - side[v];
                    Rbuf[qt++] = u;
                } else if (side[u] == side[v]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    int cur = eval_cost();
    if (cur == 0) snapshot();
    int stag = 0, round_min = 1 << 30;
    long long it = 0;
    const int STAG_LIMIT = 4000;

    while (1) {
        if ((it & 7) == 0 && wall() - t_start > t_budget) break;
        it++;
        if (cur == 0) {
            if (n > best_n) snapshot();
            if (grow_one()) {
                fill_all();
                cur = eval_cost();
            } else {
                cur = restart_state();
            }
            stag = 0;
            round_min = 1 << 30;
            continue;
        }
        int a, b, c, e;
        if (!pick_swap(&a, &b, &c, &e)) continue;
        do_swap(a, b, c, e);
        int nc = eval_cost();
        if (nc <= cur || urand() < exp(-(double)(nc - cur) / temp)) {
            cur = nc;
        } else {
            undo_swap(a, b, c, e);
        }
        if (cur < round_min) {
            round_min = cur;
            stag = 0;
        } else if (++stag > STAG_LIMIT) {
            cur = restart_state();
            stag = 0;
            round_min = 1 << 30;
        }
    }

    if (best_n <= 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", snap_eu[i], snap_ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
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
    """Dense structured graph (degree at least d) used as a thinning source."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover all vertices within D."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices, then saturate edges with spare degree."""
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
    """Add non-adjacent twins while neighbours have spare degree."""
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
            nbrs = adj[v]
            if not nbrs or len(nbrs) > d:
                continue
            if any(len(adj[u]) >= d for u in nbrs):
                continue
            w = len(adj)
            adj.append(set(nbrs))
            for u in nbrs:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
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
    """Delete the worst vertices in batches until the diameter bound holds."""
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
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
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
    """Thin a dense structured graph into a valid one, then regrow."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver.
#   Python: structured base, cover growth, twin trials, thinning (short).
#   C:      simulated annealing on bad-pair cost with degree-preserving swaps,
#           cover-vertex growth whenever the cost is zero, and restart-from-best
#           perturbation (LNS) until the budget is spent.
# Every candidate is checked by lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured bases.
    cands = []
    if D >= 4:
        g = _best_gq(d)
        if g is not None:
            cands.append(g)
    if D >= 3:
        g = _best_pg(d)
        if g is not None:
            cands.append(g)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
    for n0, e0 in cands:
        consider(n0, e0)

    if best_n >= moore:
        return best_n, list(best_e)

    base_n, base_e = best_n, list(best_e)

    # Phase 1: grow the structured base by covers and saturation.
    if D >= 3 and base_n > 2 * d:
        n1, e1 = _grow(base_n, base_e, d, D, at(0.06), rng)
        consider(n1, e1)

    # Phase 2: randomized twin / cover trials.
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase 3: thinned dense structured graph (short).
    if D >= 2 and time.monotonic() < at(0.20):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.20):
                r = _deletion_trial(d, D, rn, re, rng, at(0.20))
                if r is None:
                    break
                consider(*r)

    # Phase 4: C annealing / LNS from the best valid graph.
    if best_n < moore:
        elapsed = time.monotonic() - start
        budget = time_limit * 0.88 - elapsed - 3.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 6.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)

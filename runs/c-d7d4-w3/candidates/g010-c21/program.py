# Merged program. Python builds the structured base (GQ W(q) for D >= 4, PG(2,q) for D = 3,
# K_{2,2}/cycle for d = 2), then runs twin-duplication trials and voltage lifts over small
# groups (Z_m and Z_m x| Z_k). The best graph so far goes to a new C engine. That engine
# works as a degree-preserving insertion-and-anneal search: it adds a bipartite vertex pair
# by swapping d disjoint edges, then anneals double-edge switches to minimise pairs at
# distance > D, using bitset BFS. Only zero-cost states are kept, and every result is
# checked with lib.is_valid. The Python best graph is the fallback.
import itertools
import math
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

static int d, D, CAP, N, snapN;
static int *deg, *adj, *side, *used, *snap_deg, *snap_adj;
static int *edge_u, *edge_v, *pick_x, *pick_y, *lstk, *Lv, *Rv;
static u64 *bufA, *bufB;
static u64 rs;

static u64 rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (u64)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > D (unreachable pairs count). */
static long long cost(void) {
    int n = N;
    int w = (n + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        u64 *r = cur + (size_t)v * w;
        for (int i = 0; i < w; i++) r[i] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int rd = 0; rd < D; rd++) {
        for (int v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * w;
            const u64 *c = cur + (size_t)v * w;
            for (int i = 0; i < w; i++) o[i] = c[i];
            const int *av = adj + (size_t)v * d;
            for (int k = 0; k < deg[v]; k++) {
                const u64 *s = cur + (size_t)av[k] * w;
                for (int i = 0; i < w; i++) o[i] |= s[i];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const u64 *r = cur + (size_t)v * w;
        int c = 0;
        for (int i = 0; i < w; i++) c += popc64(r[i]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_arc(int x, int y) {
    const int *ax = adj + (size_t)x * d;
    for (int k = 0; k < deg[x]; k++) if (ax[k] == y) return 1;
    return 0;
}

static void push_arc(int x, int y) {
    adj[(size_t)x * d + deg[x]] = y;
    deg[x]++;
}

static void del_arc(int x, int y) {
    int *ax = adj + (size_t)x * d;
    for (int k = 0; k < deg[x]; k++) {
        if (ax[k] == y) {
            ax[k] = ax[deg[x] - 1];
            deg[x]--;
            return;
        }
    }
}

static void repl_arc(int x, int old, int nw) {
    int *ax = adj + (size_t)x * d;
    for (int k = 0; k < deg[x]; k++) {
        if (ax[k] == old) { ax[k] = nw; return; }
    }
}

/* Add cross edges between deficient vertices (only lowers the cost). */
static void saturate(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) Lv[nl++] = v;
            else Rv[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    long tries = 100L * (nl + nr);
    for (long t = 0; t < tries; t++) {
        int a = Lv[rndint(nl)], b = Rv[rndint(nr)];
        if (deg[a] >= d || deg[b] >= d || has_arc(a, b)) continue;
        push_arc(a, b);
        push_arc(b, a);
    }
}

/* Degree-preserving insertion of one new vertex pair a (side 0), b (side 1). */
static int insert_pair(void) {
    if (N + 2 > CAP) return 0;
    int m = 0;
    for (int x = 0; x < N; x++) {
        if (side[x] != 0) continue;
        for (int k = 0; k < deg[x]; k++) {
            edge_u[m] = x;
            edge_v[m] = adj[(size_t)x * d + k];
            m++;
        }
    }
    if (m < d) return 0;
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tu = edge_u[i], tv = edge_v[i];
        edge_u[i] = edge_u[j];
        edge_v[i] = edge_v[j];
        edge_u[j] = tu;
        edge_v[j] = tv;
    }
    for (int v = 0; v < N; v++) used[v] = 0;
    int picked = 0;
    for (int i = 0; i < m && picked < d; i++) {
        int x = edge_u[i], y = edge_v[i];
        if (used[x] || used[y]) continue;
        used[x] = 1;
        used[y] = 1;
        pick_x[picked] = x;
        pick_y[picked] = y;
        picked++;
    }
    if (picked < d) return 0;
    int a = N, b = N + 1;
    N += 2;
    side[a] = 0;
    side[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    for (int i = 0; i < d; i++) {
        int x = pick_x[i], y = pick_y[i];
        del_arc(x, y);
        del_arc(y, x);
        push_arc(a, y);
        push_arc(y, a);
        push_arc(x, b);
        push_arc(b, x);
    }
    return 1;
}

static void snapshot(void) {
    snapN = N;
    memcpy(snap_deg, deg, sizeof(int) * (size_t)N);
    memcpy(snap_adj, adj, sizeof(int) * (size_t)N * d);
}

static void restore(void) {
    N = snapN;
    memcpy(deg, snap_deg, sizeof(int) * (size_t)N);
    memcpy(adj, snap_adj, sizeof(int) * (size_t)N * d);
}

/* Double-edge switches (a-b, c-e) -> (a-e, c-b) with a, c on side 0. Keeps degrees. */
static long long anneal(long long cur, long iters, double deadline) {
    double temp = 0.5;
    for (long it = 0; it < iters && cur > 0; it++) {
        if (now() > deadline) break;
        if (temp > 0.05) temp *= 0.999;
        int a = -1, c = -1, t2 = 0;
        do {
            a = rndint(N);
            t2++;
        } while ((side[a] != 0 || deg[a] == 0) && t2 < 1000);
        if (side[a] != 0 || deg[a] == 0) break;
        t2 = 0;
        do {
            c = rndint(N);
            t2++;
        } while ((side[c] != 0 || deg[c] == 0 || c == a) && t2 < 1000);
        if (side[c] != 0 || deg[c] == 0 || c == a) break;
        int b = adj[(size_t)a * d + rndint(deg[a])];
        int e = adj[(size_t)c * d + rndint(deg[c])];
        if (has_arc(a, e) || has_arc(c, b)) continue;
        repl_arc(a, b, e);
        repl_arc(b, a, c);
        repl_arc(c, e, b);
        repl_arc(e, c, a);
        long long nw = cost();
        if (nw <= cur || rnd01() < exp((double)(cur - nw) / temp)) {
            cur = nw;
        } else {
            repl_arc(a, e, b);
            repl_arc(e, a, c);
            repl_arc(c, b, e);
            repl_arc(b, c, a);
        }
    }
    return cur;
}

static void emit_input(int n0, int m0, const int *eu, const int *ev, int from_empty) {
    if (from_empty) {
        printf("1 0\n");
        return;
    }
    printf("%d %d\n", n0, m0);
    for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 88172645463325252ULL;
    for (int i = 0; i < 8; i++) rnd64();
    double tl = atof(argv[4]);
    double t_end = 0.88 * tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("1 0\n"); return 0; }
    if (d < 2 || D < 2 || n0 < 0 || m0 < 0) { printf("1 0\n"); return 0; }
    int from_empty = (n0 == 0);
    int *eu = NULL, *ev = NULL;
    if (from_empty) {
        n0 = 2 * d;
        m0 = d * d;
        eu = malloc(sizeof(int) * (size_t)m0);
        ev = malloc(sizeof(int) * (size_t)m0);
        int k = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                eu[k] = i;
                ev[k] = d + j;
                k++;
            }
    } else {
        eu = malloc(sizeof(int) * (size_t)(m0 + 1));
        ev = malloc(sizeof(int) * (size_t)(m0 + 1));
        int got = 0;
        for (; got < m0; got++) {
            if (scanf("%d %d", &eu[got], &ev[got]) != 2) break;
        }
        m0 = got;
    }

    double mo = 0.0, term = 1.0;
    for (int i = 0; i < D; i++) {
        mo += term;
        term *= (double)(d - 1);
    }
    mo *= 2.0;
    double capd = mo + 4.0;
    if (capd > 20000.0) capd = 20000.0;
    CAP = (int)capd;
    if (CAP < n0 + 4) CAP = n0 + 4;

    int Wc = (CAP + 63) >> 6;
    deg = calloc((size_t)CAP, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    used = calloc((size_t)CAP, sizeof(int));
    lstk = calloc((size_t)CAP, sizeof(int));
    Lv = calloc((size_t)CAP, sizeof(int));
    Rv = calloc((size_t)CAP, sizeof(int));
    snap_deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * d, sizeof(int));
    snap_adj = calloc((size_t)CAP * d, sizeof(int));
    edge_u = calloc((size_t)CAP * d + 4, sizeof(int));
    edge_v = calloc((size_t)CAP * d + 4, sizeof(int));
    pick_x = calloc((size_t)d + 1, sizeof(int));
    pick_y = calloc((size_t)d + 1, sizeof(int));
    bufA = calloc((size_t)CAP * Wc, sizeof(u64));
    bufB = calloc((size_t)CAP * Wc, sizeof(u64));
    if (!deg || !side || !used || !lstk || !Lv || !Rv || !snap_deg || !adj ||
        !snap_adj || !edge_u || !edge_v || !pick_x || !pick_y || !bufA || !bufB ||
        !eu || !ev) {
        printf("1 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int x = eu[i], y = ev[i];
        if (x < 0 || x >= N || y < 0 || y >= N || x == y ||
            deg[x] >= d || deg[y] >= d || has_arc(x, y)) {
            printf("1 0\n");
            return 0;
        }
        push_arc(x, y);
        push_arc(y, x);
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        lstk[sp++] = s;
        while (sp > 0) {
            int u = lstk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * d + k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    lstk[sp++] = v;
                }
            }
        }
    }

    saturate();
    long long c = cost();
    if (c > 0) c = anneal(c, 200000L, t_end);
    if (c != 0) {
        emit_input(n0, m0, eu, ev, from_empty);
        return 0;
    }

    const long ITERS = 2500L;
    while (now() < t_end) {
        snapshot();
        if (!insert_pair()) break;
        long long cc = cost();
        cc = anneal(cc, ITERS, t_end);
        if (cc == 0) saturate();
        else restore();
    }

    if (cost() != 0) {
        emit_input(n0, m0, eu, ev, from_empty);
        return 0;
    }
    long long mm = 0;
    for (int v = 0; v < N; v++) mm += deg[v];
    mm /= 2;
    printf("%d %lld\n", N, mm);
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[(size_t)v * d + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
"""


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


# ----------------------------------------------------------------------------
# Twin duplication and pipelines.
# ----------------------------------------------------------------------------

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
# Voltage lifts over small groups (Python stage).
# ----------------------------------------------------------------------------

def _group_specs(lo, hi):
    specs = [("cyc", n) for n in range(lo, hi + 1)]
    for k in range(2, 13):
        for m in range(2, hi // k + 1):
            if not (lo <= m * k <= hi):
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append(("semi", m, k, r))
    return specs


def _make_group(spec):
    if spec[0] == "cyc":
        return lib.cyclic_group(spec[1])
    _, m, k, r = spec
    return lib.semidirect_group(m, k, r)


def _random_base(a, d, rng, order):
    left = [i for i in range(a) for _ in range(d)]
    right = list(left)
    rng.shuffle(right)
    return [[left[k], right[k], rng.randrange(order)] for k in range(len(left))]


def _lift_adj(a, order, darts, R):
    N = 2 * a * order
    off = a * order
    adj = [[] for _ in range(N)]
    for i, j, g in darts:
        Rg = R[g]
        ba = i * order
        bb = off + j * order
        for x in range(order):
            u = ba + x
            v = bb + Rg[x]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _lift_cost(adj, a, order, D):
    N = len(adj)
    total = 0
    sources = [i * order for i in range(a)] + [a * order + j * order for j in range(a)]
    for s in sources:
        seen = [False] * N
        seen[s] = True
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _lift_edges(a, order, darts, R):
    off = a * order
    E = set()
    for i, j, g in darts:
        Rg = R[g]
        for x in range(order):
            E.add((i * order + x, off + j * order + Rg[x]))
    return sorted(E)


def _voltage_search(a, d, D, order, R, rng, iters, deadline):
    darts = _random_base(a, d, rng, order)
    cur = _lift_cost(_lift_adj(a, order, darts, R), a, order, D)
    for _ in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        new = [list(x) for x in darts]
        if rng.random() < 0.7:
            new[rng.randrange(len(new))][2] = rng.randrange(order)
        else:
            k1 = rng.randrange(len(new))
            k2 = rng.randrange(len(new))
            new[k1][1], new[k2][1] = new[k2][1], new[k1][1]
        c2 = _lift_cost(_lift_adj(a, order, new, R), a, order, D)
        if c2 <= cur or rng.random() < 0.02:
            darts, cur = new, c2
    return darts if cur == 0 else None


def _lift_stage(d, D, get_best, rng, deadline, consider):
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        best = get_best()
        avail = [a for a in (1, 2) if best // (2 * a) + 1 <= moore // (2 * a)]
        if not avail:
            return
        a = rng.choice(avail)
        lo = best // (2 * a) + 1
        hi = min(moore // (2 * a), lo + 60)
        specs = _group_specs(lo, hi)
        if not specs:
            return
        spec = rng.choice(specs)
        order, mul, _ = _make_group(spec)
        R = [[mul(x, g) for x in range(order)] for g in range(order)]
        darts = _voltage_search(a, d, D, order, R, rng, 1500, deadline)
        if darts is not None:
            consider(2 * a * order, _lift_edges(a, order, darts, R))


# ----------------------------------------------------------------------------
# Driver.
# Timeline (fractions of time_limit): base and grow to 0.05, twin trials to 0.12,
# voltage lifts to 0.30, C insertion-anneal engine until 0.88, hard wall 0.92.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    state = {"n": fallback[0], "e": list(fallback[1])}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"] = n
            state["e"] = list(e)
            return True
        return False

    def result():
        if not lib.is_valid(state["n"], state["e"], d, D):
            return fallback
        return state["n"], list(state["e"])

    moore = lib.moore_bound(d, D)
    if d == 2 and D >= 2:
        consider(*lib.haar_graph(D, [0, 1]))  # cycle of length 2D, Moore-optimal
    if state["n"] >= moore:
        return result()

    # Structured base.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
        consider(n1, e1)
    seed_n, seed_e = base if base is not None else fallback

    # Randomized twin-duplication pipelines.
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end and state["n"] < moore:
            n, e = _trial(seed_n, list(seed_e), d, D, rng, trial_end)
            consider(n, e)

    # Voltage lifts over small groups.
    if D >= 2 and state["n"] < moore and time.monotonic() < at(0.30):
        _lift_stage(d, D, lambda: state["n"], rng, at(0.30), consider)

    # C insertion-and-anneal engine from the best valid graph so far.
    if D >= 2 and state["n"] < moore:
        hard = at(0.92)
        c_budget = at(0.88) - time.monotonic() - 1.5  # leave room for the compile
        if c_budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=(state["n"], state["e"]),
                                timeout=max(2.0, hard - time.monotonic()))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    return result()

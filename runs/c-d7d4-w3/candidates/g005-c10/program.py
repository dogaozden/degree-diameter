import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: starts from a valid graph and repeatedly
#   (1) adds a vertex whose same-side-opposite neighbours (<= d of them) have
#       radius-(D-1) balls covering the whole graph (greedy randomised cover),
#   (2) saturates spare degree with random opposite-side edges (never hurts
#       the diameter),
#   (3) when stuck, kicks: removes random edges while the diameter stays <= D,
#       which frees degree for the next vertex addition.
# It keeps the best graph seen and reloads it after a long stall.
# Output: "n m" followed by m edge lines. Python re-validates every answer.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1536
#define NW 24
#define MAXDEG 40
#define MAXE 40000

typedef uint64_t u64;

static int N, DEG, DD, nw;
static int deg[MAXN], nb[MAXN][MAXDEG], col[MAXN];
static u64 BA[MAXN][NW], BB[MAXN][NW], BALL[MAXN][NW], BALLD[MAXN][NW];
static u64 rs;
static unsigned char PC16[65536];
static char used[MAXN];

static int bestN, bestM, bestCol[MAXN], bestEu[MAXE], bestEv[MAXE];

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (u64)k); }

static int pc64(u64 x) {
    return PC16[x & 0xFFFF] + PC16[(x >> 16) & 0xFFFF] +
           PC16[(x >> 32) & 0xFFFF] + PC16[x >> 48];
}

static int pcrow(const u64 *r) {
    int c = 0;
    for (int w = 0; w < nw; w++) c += pc64(r[w]);
    return c;
}

static void set_n(int n) {
    N = n;
    nw = (N + 63) / 64;
}

static int is_adj(int a, int b) {
    for (int j = 0; j < deg[a]; j++)
        if (nb[a][j] == b) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_half(int u, int v) {
    for (int j = 0; j < deg[u]; j++) {
        if (nb[u][j] == v) {
            nb[u][j] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

/* out[v] = bitmask of vertices at distance <= r from v. */
static void compute_balls(int r, u64 out[MAXN][NW]) {
    for (int v = 0; v < N; v++) {
        memset(BA[v], 0, sizeof(BA[v]));
        BA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) BB[v][w] = BA[v][w];
            for (int j = 0; j < deg[v]; j++) {
                const u64 *src = BA[nb[v][j]];
                for (int w = 0; w < nw; w++) BB[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < nw; w++) BA[v][w] = BB[v][w];
    }
    for (int v = 0; v < N; v++)
        for (int w = 0; w < nw; w++) out[v][w] = BA[v][w];
}

static int diam_ok(void) {
    compute_balls(DD, BALLD);
    for (int v = 0; v < N; v++)
        if (pcrow(BALLD[v]) != N) return 0;
    return 1;
}

/* Greedy randomised cover: choose up to DEG candidates of colour 1-x
   (with spare degree) whose radius-(DD-1) balls cover all N vertices. */
static int try_cover(int x, int *chosen) {
    u64 cov[NW];
    memset(cov, 0, sizeof(cov));
    memset(used, 0, sizeof(used));
    int picked = 0, have = 0;
    while (picked < DEG && have < N) {
        int best = -1, bestg = 0, ties = 0;
        for (int t = 0; t < N; t++) {
            if (used[t] || col[t] == x || deg[t] >= DEG) continue;
            int g = 0;
            for (int w = 0; w < nw; w++) g += pc64(BALL[t][w] & ~cov[w]);
            if (g > bestg) {
                bestg = g;
                best = t;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndint(ties) == 0) best = t;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[picked++] = best;
        for (int w = 0; w < nw; w++) cov[w] |= BALL[best][w];
        have = 0;
        for (int w = 0; w < nw; w++) have += pc64(cov[w]);
    }
    return have == N ? picked : -1;
}

static int add_vertex(int x) {
    int chosen[MAXDEG];
    if (N >= MAXN - 1) return 0;
    for (int att = 0; att < 12; att++) {
        int k = try_cover(x, chosen);
        if (k > 0) {
            int v = N;
            set_n(N + 1);
            col[v] = x;
            deg[v] = 0;
            for (int i = 0; i < k; i++) {
                int s = chosen[i];
                nb[s][deg[s]++] = v;
                nb[v][deg[v]++] = s;
            }
            return 1;
        }
    }
    return 0;
}

static void saturate(void) {
    int tries = 8 * N;
    while (tries-- > 0) {
        int a = rndint(N), b = rndint(N);
        if (col[a] == col[b] || deg[a] >= DEG || deg[b] >= DEG) continue;
        if (is_adj(a, b)) continue;
        add_edge(a, b);
    }
}

static void kick(void) {
    int u = rndint(N);
    if (deg[u] == 0) return;
    int v = nb[u][rndint(deg[u])];
    del_half(u, v);
    del_half(v, u);
    if (!diam_ok()) add_edge(u, v);
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int u = 0; u < N; u++) {
        bestCol[u] = col[u];
        for (int j = 0; j < deg[u]; j++) {
            int v = nb[u][j];
            if (u < v && bestM < MAXE) {
                bestEu[bestM] = u;
                bestEv[bestM] = v;
                bestM++;
            }
        }
    }
}

static void load_best(void) {
    set_n(bestN);
    for (int u = 0; u < N; u++) {
        deg[u] = 0;
        col[u] = bestCol[u];
    }
    for (int i = 0; i < bestM; i++) add_edge(bestEu[i], bestEv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)strtoull(argv[3], NULL, 10) * 0xBF58476D1CE4E5B9ULL);
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < 65536; i++)
        PC16[i] = (i == 0) ? 0 : (unsigned char)(PC16[i >> 1] + (i & 1));

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 64) {
        printf("0 0\n");
        return 0;
    }
    set_n(n);
    for (int u = 0; u < N; u++) deg[u] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
            deg[u] >= DEG || deg[v] >= DEG || is_adj(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    for (int u = 0; u < N; u++) col[u] = -1;
    static int stk[MAXN];
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int j = 0; j < deg[u]; j++) {
                int v = nb[u][j];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    if (!diam_ok()) {
        printf("0 0\n");
        return 0;
    }

    save_best();
    clock_t t0 = clock();
    int stall = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
        compute_balls(DD - 1, BALL);
        int first = rndint(2), grew = 0;
        for (int k = 0; k < 2 && !grew; k++)
            grew = add_vertex(k == 0 ? first : 1 - first);
        if (grew) {
            saturate();
            if (N > bestN) {
                save_best();
                stall = 0;
            }
            continue;
        }
        for (int t = 0; t < 10; t++) kick();
        saturate();
        if (++stall > 300) {
            load_best();
            stall = 0;
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
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


# ----------------------------------------------------------------------------
# Shared Python helpers.
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
# Bipartite voltage lifts over small (semi-direct) groups, annealed to
# diameter <= D. Parked runs are resumed in later slices.
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples: cyclic group plus Z_M x|_r Z_k with M*k = G."""
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


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    """Anneal voltages. Returns (result, darts, temp); result is (n, edges) or None."""
    if darts is None:
        darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None, darts, temp
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
    return (n, e), darts, temp


def _lift_phase(d, D, get_best, deadline, rng, consider):
    states = {}  # key (s, G, M, k, r) -> (darts, temp)
    while time.monotonic() < deadline:
        best_n = get_best()
        states = {key: v for key, v in states.items() if 2 * key[0] * key[1] > best_n}
        if states and rng.random() < 0.7:
            key = rng.choice(list(states))
            darts, temp = states.pop(key)
            s, G, M, k, r = key
        else:
            darts, temp = None, 0.6
            s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
            G_min = best_n // (2 * s) + 1
            G = G_min + rng.randrange(4)
            opts = _group_options(G)
            if not opts:
                continue
            M, k, r = rng.choice(opts)
            key = (s, G, M, k, r)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res, darts, temp = _lift_search(d, D, s, G, mul, rng, slice_end, darts, temp)
        if res is None:
            states[key] = (darts, temp)
            if len(states) > 40:
                states.pop(next(iter(states)))
            continue
        n, e = res
        consider(n, e)
        n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) for D >= 4, PG(2,q) for D = 3), grown, then twin trials
#   L  voltage lifts over small groups
#   C  C engine (cover-extension + diameter-preserving kicks) from the best graph
# Every candidate passes lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    def at(f):
        return start + f * time_limit

    fallback = (2, [(0, 1)])
    hn, he = lib.haar_graph(d, range(d))
    if lib.is_valid(hn, he, d, D):
        fallback = (hn, he)
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
        if lib.is_valid(n0, e0, d, D):
            base_n, base_e = n0, list(e0)
        n1, e1 = _grow(base_n, base_e, d, D, at(0.10), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.18)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.30):
        _lift_phase(d, D, lambda: best_n, at(0.30), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: C engine from the best valid graph found so far.
    c_deadline = at(0.93)
    cb = c_deadline - time.monotonic() - 1.5  # margin for the first compile
    if D >= 2 and cb > 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{cb:.2f}"],
                            stdin_graph=(best_n, best_e),
                            timeout=max(1.0, at(0.97) - time.monotonic()))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)

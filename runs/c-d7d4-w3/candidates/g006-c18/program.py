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

#define MAXN 1100
#define MAXW 18
#define MAXDEG 40
#define MAXE (MAXN * MAXDEG)

typedef uint64_t u64;

static int N = 0, d = 1, D = 2;
static unsigned char A[MAXN][MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static int col[MAXN];
static u64 ball[MAXN][MAXW];
static u64 tmpb[MAXN][MAXW];
static unsigned long long rs = 88172645463325252ULL;
static int CU[MAXE], CV[MAXE], BU[MAXE], BV[MAXE], TU[MAXE], TV[MAXE];
static int cn, bn, cm, bm;

static unsigned long long rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int m) {
    if (m <= 1) return 0;
    return (int)(rnd64() % (unsigned long long)m);
}
static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void clear_graph(void) {
    for (int u = 0; u < N; u++) {
        for (int w = 0; w < N; w++) A[u][w] = 0;
        deg[u] = 0;
    }
    N = 0;
}

static void addE(int u, int v) {
    A[u][v] = 1; A[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void delNb(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void delE(int u, int v) {
    A[u][v] = 0; A[v][u] = 0;
    delNb(u, v);
    delNb(v, u);
}

static void set_graph(int n, int m, const int *eu, const int *ev) {
    clear_graph();
    N = n;
    for (int u = 0; u < N; u++) { deg[u] = 0; col[u] = -1; }
    for (int i = 0; i < m; i++) addE(eu[i], ev[i]);
    static int q[MAXN];
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int i = 0; i < deg[x]; i++) {
                int y = nb[x][i];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; }
            }
        }
    }
}

static long cost(void) {
    int Wn = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < Wn; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < Wn; w++) tmpb[v][w] = ball[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < Wn; w++) tmpb[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < Wn; w++) ball[v][w] = tmpb[v][w];
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < Wn; w++) c += popc(ball[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Degree-preserving bipartite switches minimising bad pairs. Returns final cost. */
static long anneal(int iters, double deadline) {
    long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && now_s() > deadline) break;
        int a = rndint(N), c = rndint(N);
        if (a == c || col[a] != 0 || col[c] != 0 || deg[a] == 0 || deg[c] == 0) continue;
        int b = nb[a][rndint(deg[a])];
        int e = nb[c][rndint(deg[c])];
        if (A[a][e] || A[c][b]) continue;
        delE(a, b); delE(c, e);
        addE(a, e); addE(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndint(10) == 0)) {
            cur = nw;
        } else {
            delE(a, e); delE(c, b);
            addE(a, b); addE(c, e);
        }
    }
    return cur;
}

/* Add cross-side edges between deficient vertices (never breaks validity). */
static void fill(void) {
    if (N <= 1) return;
    int a0 = rndint(N);
    int off = rndint(N);
    for (int k = 0; k < N; k++) {
        int a = (a0 + k) % N;
        if (deg[a] >= d) continue;
        for (int i = 0; i < N && deg[a] < d; i++) {
            int b = (i + off) % N;
            if (col[b] == col[a] || A[a][b] || deg[b] >= d) continue;
            addE(a, b);
        }
    }
}

/* Add a vertex on the side opposite `side`, joined to d random vertices of `side`. */
static void add_vertex(int side) {
    int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < N; u++) if (col[u] == side) cand[nc++] = u;
    int v = N;
    N++;
    deg[v] = 0;
    col[v] = 1 - side;
    int k = d < nc ? d : nc;
    for (int i = 0; i < k; i++) {
        int j = i + rndint(nc - i);
        int tmp = cand[i]; cand[i] = cand[j]; cand[j] = tmp;
    }
    for (int i = 0; i < k; i++) {
        int s = cand[i];
        if (deg[s] >= d) {
            int t = nb[s][rndint(deg[s])];
            delE(s, t);
        }
        addE(s, v);
    }
}

static void compact_remove(const int *kill, int nk) {
    static int map[MAXN];
    static int isk[MAXN];
    for (int i = 0; i < N; i++) isk[i] = 0;
    for (int i = 0; i < nk; i++) isk[kill[i]] = 1;
    int m = 0;
    for (int v = 0; v < N; v++) map[v] = isk[v] ? -1 : m++;
    int ne = 0;
    for (int u = 0; u < N; u++) {
        if (map[u] < 0) continue;
        for (int i = 0; i < deg[u]; i++) {
            int w = nb[u][i];
            if (u < w && map[w] >= 0) {
                TU[ne] = map[u];
                TV[ne] = map[w];
                ne++;
            }
        }
    }
    set_graph(m, ne, TU, TV);
}

static int export_graph(int *eu, int *ev) {
    int m = 0;
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int w = nb[u][i];
            if (u < w) { eu[m] = u; ev[m] = w; m++; }
        }
    }
    return m;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (unsigned long long)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = now_s() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN || m < 0 || m > MAXE ||
        d < 1 || d > MAXDEG || D < 1) {
        printf("1 0\n");
        return 0;
    }
    static int dc[MAXN];
    for (int i = 0; i < n; i++) dc[i] = 0;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &CU[i], &CV[i]) != 2) { printf("1 0\n"); return 0; }
        if (CU[i] < 0 || CU[i] >= n || CV[i] < 0 || CV[i] >= n || CU[i] == CV[i]) {
            printf("1 0\n"); return 0;
        }
        dc[CU[i]]++; dc[CV[i]]++;
    }
    for (int i = 0; i < n; i++) if (dc[i] > d) { printf("1 0\n"); return 0; }

    set_graph(n, m, CU, CV);
    for (int i = 0; i < m; i++) {
        if (col[CU[i]] == col[CV[i]]) { printf("1 0\n"); return 0; }
    }
    if (cost() != 0) { printf("1 0\n"); return 0; }

    cn = N;
    cm = export_graph(CU, CV);
    bn = cn; bm = cm;
    memcpy(BU, CU, sizeof(int) * (size_t)cm);
    memcpy(BV, CV, sizeof(int) * (size_t)cm);

    while (now_s() < deadline) {
        int type = (N < 4 || rndint(10) < 6) ? 0 : 1;
        if (type == 0) {
            if (N + 1 >= MAXN) break;
            add_vertex(rndint(2));
        } else {
            int kill[2];
            int nk = 1 + rndint(2);
            if (nk >= N - 1) nk = 1;
            int got = 0;
            while (got < nk) {
                int x = rndint(N);
                if (got == 1 && kill[0] == x) continue;
                kill[got++] = x;
            }
            compact_remove(kill, nk);
        }
        fill();
        long c = anneal(type == 0 ? 1500 : 600, deadline);
        int accept = (c == 0) && (type == 0 || N >= cn - 1);
        if (accept) {
            cn = N;
            cm = export_graph(CU, CV);
            if (cn > bn) {
                bn = cn; bm = cm;
                memcpy(BU, CU, sizeof(int) * (size_t)cm);
                memcpy(BV, CV, sizeof(int) * (size_t)cm);
            }
        } else {
            set_graph(cn, cm, CU, CV);
        }
        /* Anchor: drifted too far below the best graph, so return to it. */
        if (cn < bn - 2 && rndint(4) == 0) {
            memcpy(CU, BU, sizeof(int) * (size_t)bm);
            memcpy(CV, BV, sizeof(int) * (size_t)bm);
            set_graph(bn, bm, CU, CV);
            cn = bn; cm = bm;
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", BU[i], BV[i]);
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Add vertices whose neighbourhoods cover all vertices within D-1 of deficient ones."""
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
            for attempt in range(attempts):
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
    """Join deficient opposite-side vertices in random order (keeps bipartite and degree bound)."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Python repair tools (used for doubling, lifts, and as a fallback if C fails).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return cur == 0


def _double_cross(n, edges, d, D, rng, deadline):
    """Two cross-matched copies of a base graph, repaired by annealing. Returns (N, edges) or None."""
    N = 2 * n
    if N > lib.moore_bound(d, D):
        return None
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    B = [set() for _ in range(N)]
    for u in range(n):
        for v in adj[u]:
            B[u].add(v)
            B[u + n].add(v + n)
    spare = [d - len(adj[v]) for v in range(n)]
    s0 = [v for v in range(n) if color[v] == 0 for _ in range(spare[v])]
    s1 = [v for v in range(n) if color[v] == 1 for _ in range(spare[v])]
    rng.shuffle(s0)
    rng.shuffle(s1)
    t0 = list(s0)
    t1 = list(s1)
    rng.shuffle(t0)
    rng.shuffle(t1)
    for x, w in zip(s0, s1):          # A colour-0 with B copies of colour-1 vertices
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    for x, w in zip(t1, t0):          # A colour-1 with B copies of colour-0 vertices
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    # The copy keeps the same colouring, so every cross edge joins opposite colours.
    color2 = color + color
    _fill(B, color2, d, rng)
    if _anneal(B, color2, d, D, rng, 300, deadline):
        return N, [(u, v) for u in range(N) for v in B[u] if u < v]
    return None


def _try_doubling(n, edges, d, D, deadline, rng, consider):
    for _ in range(5):
        if time.monotonic() >= deadline:
            break
        res = _double_cross(n, edges, d, D, rng, deadline)
        if res is not None:
            consider(*res)
            return True
    return False


def _random_lift2(n, edges, rng):
    """Random Z_2 lift: each edge (u, v) becomes two edges, with a random twist. Lifts of bipartite graphs stay bipartite."""
    out = []
    for u, v in edges:
        s = rng.randrange(2)
        for i in range(2):
            out.append((u + n * i, v + n * (i ^ s)))
    return 2 * n, out


def _lift_search(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        n2, e2 = _random_lift2(cur_n, cur_e, rng)
        adj = _to_sets(n2, e2)
        color = _bipartition(n2, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 300, deadline):
            continue
        e3 = [(u, v) for u in range(n2) for v in adj[u] if u < v]
        n4, e4 = _grow(n2, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > cur_n and lib.is_valid(n4, e4, d, D):
            cur_n, cur_e = n4, e4


def _repair(d, D, n, edges, deadline, rng, consider):
    """Python fallback: repeatedly add one vertex and repair with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# C engine driver.
# ----------------------------------------------------------------------------

def _c_engine(d, D, n, edges, seed, budget):
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 10.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    base_n, base_e = best_n, list(best_e)

    # Algebraic-style families, only when they can fit under the Moore bound.
    if D >= 2 and 2 * base_n <= lib.moore_bound(d, D):
        _try_doubling(base_n, base_e, d, D, start + 0.20 * time_limit, rng, consider)
        _lift_search(base_n, base_e, d, D, start + 0.30 * time_limit, rng, consider)

    # Randomized twin / cover / saturation pipelines (cheap diversity).
    if D >= 2:
        trial_end = start + 0.36 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Main search: C engine (add-vertex / kill-repair / anchored walk) from the best graph.
    c_done = False
    if D >= 2 and time.monotonic() < deadline - 2.0:
        try:
            n, e = _c_engine(d, D, best_n, best_e, seed,
                             deadline - time.monotonic() - 1.5)
            consider(n, e)
            c_done = True
        except Exception:
            c_done = False

    # Python fallback if the C engine could not run.
    if D >= 2 and not c_done and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)

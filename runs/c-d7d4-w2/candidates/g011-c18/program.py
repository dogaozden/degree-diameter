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

#define MAXN 1200
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 40
#define MAXE (MAXN * MAXDEG / 2 + 64)

typedef uint64_t u64;
typedef u64 Bits[MAXW];

static int n, m, d, D;
static int eu[MAXE], ev[MAXE];
static int col[MAXN], deg[MAXN];
static unsigned char A[MAXN][MAXN];
static Bits BUF0[MAXN], BUF1[MAXN], BALL[MAXN];
static unsigned char PT[65536];
static int inc_buf[MAXE];
static u64 rs = 88172645463325252ULL;

typedef struct {
    int n, m;
    int eu[MAXE], ev[MAXE];
    int col[MAXN];
} Snap;
static Snap base_s, best_s;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc64(u64 y) {
    return PT[y & 0xffff] + PT[(y >> 16) & 0xffff] + PT[(y >> 32) & 0xffff] + PT[(y >> 48) & 0xffff];
}

static int countbits(const u64 *x, int wn) {
    int c = 0;
    for (int w = 0; w < wn; w++) c += pc64(x[w]);
    return c;
}

static void set_edge(int u, int v, int val) {
    A[u][v] = A[v][u] = (unsigned char)val;
}

static void recalc(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int e = 0; e < m; e++) { deg[eu[e]]++; deg[ev[e]]++; }
}

static void add_pair(int s, int t) {
    int a = s, b = t;
    if (col[s] != 0) { a = t; b = s; }
    eu[m] = a; ev[m] = b; m++;
    set_edge(a, b, 1);
}

static void del_idx(int i) {
    set_edge(eu[i], ev[i], 0);
    m--;
    eu[i] = eu[m];
    ev[i] = ev[m];
}

/* out[v] = bitset of vertices within distance `steps` of v */
static void compute_reach(int steps, Bits *out) {
    int wn = (n + 63) / 64;
    Bits *cur = BUF0, *nxt = BUF1, *tmp;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(Bits));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < steps; s++) {
        for (int v = 0; v < n; v++) memcpy(nxt[v], cur[v], (size_t)wn * 8);
        for (int e = 0; e < m; e++) {
            int u = eu[e], v = ev[e];
            for (int w = 0; w < wn; w++) {
                nxt[u][w] |= cur[v][w];
                nxt[v][w] |= cur[u][w];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    for (int v = 0; v < n; v++) memcpy(out[v], cur[v], (size_t)wn * 8);
}

/* number of unordered pairs at distance > D (unreachable counts) */
static long cost_fn(void) {
    int wn = (n + 63) / 64;
    compute_reach(D, BALL);
    long bad = 0;
    for (int v = 0; v < n; v++) bad += n - countbits(BALL[v], wn);
    return bad / 2;
}

static void kill_vertex(int x) {
    for (int e = m - 1; e >= 0; e--)
        if (eu[e] == x || ev[e] == x) del_idx(e);
    int L = n - 1;
    if (x != L) {
        for (int e = 0; e < m; e++) {
            if (eu[e] == L) eu[e] = x;
            if (ev[e] == L) ev[e] = x;
        }
        for (int k = 0; k < n; k++) A[x][k] = A[L][k];
        for (int k = 0; k < n; k++) A[k][x] = A[k][L];
        col[x] = col[L];
    }
    for (int k = 0; k < n; k++) { A[L][k] = 0; A[k][L] = 0; }
    n--;
    recalc();
}

/* new vertex on colour 1-side, joined to a greedy cover of radius D-1 balls on `side` */
static int add_vertex(int side) {
    if (n >= MAXN || m + d + 2 >= MAXE) return -1;
    int old = n;
    int wn = (n + 63) / 64;
    compute_reach(D - 1, BALL);
    Bits full, cov;
    memset(full, 0, sizeof(Bits));
    memset(cov, 0, sizeof(Bits));
    for (int w = 0; w < old; w++) full[w >> 6] |= 1ULL << (w & 63);
    int chosen[MAXDEG];
    int nc = 0;
    for (int it = 0; it < d && nc < d; it++) {
        int best = -1;
        long bests = -1, bestg = 0;
        for (int s = 0; s < old; s++) {
            if (col[s] != side) continue;
            int taken = 0;
            for (int k = 0; k < nc; k++) if (chosen[k] == s) { taken = 1; break; }
            if (taken) continue;
            long g = 0;
            for (int w = 0; w < wn; w++) g += pc64(BALL[s][w] & full[w] & ~cov[w]);
            long score = g * 8 + rndint(8);
            if (score > bests) { bests = score; best = s; bestg = g; }
        }
        if (best < 0 || bestg <= 0) break;
        chosen[nc++] = best;
        for (int w = 0; w < wn; w++) cov[w] |= BALL[best][w];
        int done = 1;
        for (int w = 0; w < wn; w++) if (full[w] & ~cov[w]) { done = 0; break; }
        if (done) break;
    }
    n++;
    col[old] = 1 - side;
    deg[old] = 0;
    for (int k = 0; k < n; k++) { A[old][k] = 0; A[k][old] = 0; }
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        recalc();
        if (deg[s] >= d) {
            int cnt = 0;
            for (int e = 0; e < m; e++) if (eu[e] == s || ev[e] == s) inc_buf[cnt++] = e;
            if (cnt > 0) del_idx(inc_buf[rndint(cnt)]);
        }
        add_pair(s, old);
    }
    recalc();
    return old;
}

/* add cross-side edges between deficient vertices (never hurts the diameter) */
static void fill(int tries) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    recalc();
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    if (!nl || !nr) return;
    for (int t = 0; t < tries && m < MAXE - 2; t++) {
        int a = L[rndint(nl)], b = R[rndint(nr)];
        if (deg[a] < d && deg[b] < d && !A[a][b]) {
            add_pair(a, b);
            deg[a]++;
            deg[b]++;
        }
    }
    recalc();
}

/* degree-preserving bipartite double-edge switches minimising bad pairs */
static long anneal(int iters, double tlim) {
    long cur = cost_fn();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now() > tlim) break;
        if (m < 2) break;
        int i = rndint(m), j = rndint(m);
        if (i == j) continue;
        int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
        if (a == c || b == e || A[a][e] || A[c][b]) continue;
        set_edge(a, b, 0);
        set_edge(c, e, 0);
        ev[i] = e;
        ev[j] = b;
        set_edge(a, e, 1);
        set_edge(c, b, 1);
        long nw = cost_fn();
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.03)) {
            cur = nw;
        } else {
            set_edge(a, e, 0);
            set_edge(c, b, 0);
            ev[i] = b;
            ev[j] = e;
            set_edge(a, b, 1);
            set_edge(c, e, 1);
        }
    }
    return cur;
}

static void save_snap(Snap *s) {
    s->n = n;
    s->m = m;
    memcpy(s->eu, eu, sizeof(int) * (size_t)m);
    memcpy(s->ev, ev, sizeof(int) * (size_t)m);
    memcpy(s->col, col, sizeof(int) * (size_t)n);
}

static void load_snap(const Snap *s) {
    for (int e = 0; e < m; e++) set_edge(eu[e], ev[e], 0);
    n = s->n;
    m = s->m;
    memcpy(eu, s->eu, sizeof(int) * (size_t)m);
    memcpy(ev, s->ev, sizeof(int) * (size_t)m);
    memcpy(col, s->col, sizeof(int) * (size_t)n);
    for (int e = 0; e < m; e++) set_edge(eu[e], ev[e], 1);
    recalc();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long sd = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = sd * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    for (int i = 1; i < 65536; i++) PT[i] = (unsigned char)(PT[i >> 1] + (i & 1));

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    static int ru[MAXE], rv[MAXE];
    int rc = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (rc < MAXE && u >= 0 && v >= 0 && u < n0 && v < n0 && u != v) {
            ru[rc] = u;
            rv[rc] = v;
            rc++;
        }
    }

    if (d < 2 || d > MAXDEG || D < 2 || n0 > MAXN || 2 * d > MAXN) {
        printf("0 0\n");
        return 0;
    }

    m = 0;
    if (n0 == 0) {
        n = 2 * d;
        for (int i = 0; i < n; i++) col[i] = (i < d) ? 0 : 1;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++)
                add_pair(i, d + j);
    } else {
        n = n0;
        for (int i = 0; i < rc; i++) {
            int u = ru[i], v = rv[i];
            if (!A[u][v]) {
                eu[m] = u;
                ev[m] = v;
                m++;
                set_edge(u, v, 1);
            }
        }
        static int q[MAXN];
        for (int i = 0; i < n; i++) col[i] = -1;
        for (int s = 0; s < n; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt) {
                int x = q[qh++];
                for (int k = 0; k < n; k++) {
                    if (A[x][k] && col[k] == -1) {
                        col[k] = 1 - col[x];
                        q[qt++] = k;
                    }
                }
            }
        }
        for (int i = 0; i < n; i++) if (col[i] < 0) col[i] = 0;
        for (int e = 0; e < m; e++) {
            if (col[eu[e]] == 1) {
                int t = eu[e];
                eu[e] = ev[e];
                ev[e] = t;
            }
        }
    }
    recalc();

    if (cost_fn() != 0) {
        printf("0 0\n");
        return 0;
    }

    save_snap(&base_s);
    save_snap(&best_s);
    int bestn = n;
    double tend = now() + budget;

    while (now() < tend) {
        int base_n = base_s.n;
        int kill_case = (rndint(100) < 30) && n > 6;
        if (kill_case) {
            int k = 1 + rndint(3);
            for (int t = 0; t < k && n > 2; t++) kill_vertex(rndint(n));
        } else {
            add_vertex(rndint(2));
        }
        fill(4 * n);
        long c = anneal(600, tend);
        int ok = (c == 0);
        if (ok) {
            if (kill_case) ok = (n >= base_n - 3);
            else ok = (n >= base_n);
        }
        if (ok) {
            save_snap(&base_s);
            if (n > bestn) {
                bestn = n;
                save_snap(&best_s);
            } else if (base_s.n < bestn - 4) {
                base_s = best_s;
                load_snap(&base_s);
            }
        } else {
            load_snap(&base_s);
        }
    }

    printf("%d %d\n", best_s.n, best_s.m);
    for (int e = 0; e < best_s.m; e++)
        printf("%d %d\n", best_s.eu[e], best_s.ev[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases and Python-side growth (safe fallback pipeline).
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
    """Generalized quadrangle W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
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
# Build: structured base, Python growth, then C kill/add/anneal search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Bold stage: C search (kill, add, anneal) from the best graph so far.
    elapsed = time.monotonic() - start
    budget = 0.80 * time_limit - elapsed - 2.0
    skip = best_n >= lib.moore_bound(d, D)
    if D >= 2 and d <= 40 and not skip and budget > 3:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, best_e), timeout=budget + 10)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)

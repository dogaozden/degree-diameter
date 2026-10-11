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
#include <math.h>

#define MAXN 2048
#define MAXW ((MAXN + 63) / 64)
#define MAXD 16
#define MAXE (MAXN * MAXD / 2 + 64)
#define ANNEAL_ITERS 1500

static int N = 0, DEG = 0, DIAM = 0;
static int nE = 0;
static int eu[MAXE], ev[MAXE];     /* eu = side-0 endpoint, ev = side-1 endpoint */
static int side[MAXN];
static int dg[MAXN];
static int adj[MAXN][MAXD];

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static uint64_t CA[MAXN * MAXW], CB[MAXN * MAXW];

static int SV_eu[MAXE], SV_ev[MAXE], SV_side[MAXN], SV_N = 0, SV_nE = 0;
static int BS_eu[MAXE], BS_ev[MAXE], BS_side[MAXN], BS_N = 0, BS_nE = 0;

static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd(void) {
    uint64_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng_state = x;
    return x;
}
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int rebuild_adj(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int i = 0; i < nE; i++) {
        int a = eu[i], b = ev[i];
        if (dg[a] >= DEG || dg[b] >= DEG) return 0;
        adj[a][dg[a]++] = b;
        adj[b][dg[b]++] = a;
    }
    return 1;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void del_adj(int x, int y) {
    for (int i = 0; i < dg[x]; i++) {
        if (adj[x][i] == y) {
            adj[x][i] = adj[x][dg[x] - 1];
            dg[x]--;
            return;
        }
    }
}

static void repl(int x, int oldv, int newv) {
    for (int i = 0; i < dg[x]; i++) {
        if (adj[x][i] == oldv) { adj[x][i] = newv; return; }
    }
}

static void add_edge(int a, int b) {  /* a is side 0, b is side 1 */
    if (nE >= MAXE) return;
    eu[nE] = a; ev[nE] = b; nE++;
    adj[a][dg[a]++] = b;
    adj[b][dg[b]++] = a;
}

static void add_cross(int x, int s) {
    if (side[x] == 0) add_edge(x, s);
    else add_edge(s, x);
}

static int find_edge(int a, int b) {
    for (int i = 0; i < nE; i++)
        if ((eu[i] == a && ev[i] == b) || (eu[i] == b && ev[i] == a)) return i;
    return -1;
}

static void remove_edge(int k) {
    int a = eu[k], b = ev[k];
    del_adj(a, b);
    del_adj(b, a);
    nE--;
    eu[k] = eu[nE];
    ev[k] = ev[nE];
}

/* Double-edge switch: (a,b),(c,e) -> (a,e),(c,b). Keeps degrees and bipartiteness. */
static int sw_i, sw_j, sw_a, sw_b, sw_c, sw_e;

static int propose_switch(void) {
    if (nE < 2) return 0;
    int i = rndint(nE), j = rndint(nE);
    if (i == j) return 0;
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    sw_i = i; sw_j = j; sw_a = a; sw_b = b; sw_c = c; sw_e = e;
    eu[i] = a; ev[i] = e;
    eu[j] = c; ev[j] = b;
    repl(a, b, e);
    repl(e, c, a);
    repl(b, a, c);
    repl(c, e, b);
    return 1;
}

static void undo_switch(void) {
    int a = sw_a, b = sw_b, c = sw_c, e = sw_e;
    eu[sw_i] = a; ev[sw_i] = b;
    eu[sw_j] = c; ev[sw_j] = e;
    repl(a, e, b);
    repl(e, a, c);
    repl(b, c, a);
    repl(c, b, e);
}

/* Bitmask balls of radius r. Result pointer is bufA or bufB. */
static const uint64_t *compute_balls(int r, uint64_t *bufA, uint64_t *bufB) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *nv = nxt + (size_t)v * W;
            const uint64_t *cv = cur + (size_t)v * W;
            memcpy(nv, cv, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *cu = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) nv[w] |= cu[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long bad_pairs(void) {
    int W = (N + 63) / 64;
    const uint64_t *B = compute_balls(DIAM, RA, RB);
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *bv = B + (size_t)v * W;
        for (int w = 0; w < W; w++) tot += popc(bv[w]);
    }
    long long bad = (long long)N * N - tot;
    return bad / 2;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (never increases distances). */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (dg[v] < DEG) {
            if (side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int x = 0; x < nl; x++) {
        int a = L[x];
        for (int y = 0; y < nr && dg[a] < DEG; y++) {
            int b = R[y];
            if (dg[b] >= DEG || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/* Add a vertex on a random side, joined to a greedy cover of the opposite side. */
static void grow_vertex(void) {
    if (N >= MAXN - 2) return;
    int sx = rndint(2);
    int cs = 1 - sx;
    int W = (N + 63) / 64;
    const uint64_t *B = compute_balls(DIAM - 1, CA, CB);
    uint64_t cov[MAXW];
    static char used[MAXN];
    int chosen[MAXD];
    int nch = 0;
    memset(cov, 0, sizeof(cov));
    memset(used, 0, (size_t)N);
    while (nch < DEG) {
        int best = -1;
        long long bestsc = -1;
        for (int s = 0; s < N; s++) {
            if (side[s] != cs || used[s]) continue;
            const uint64_t *bs = B + (size_t)s * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(bs[w] & ~cov[w]);
            if (g == 0) continue;
            long long sc = (long long)g * 4 + (dg[s] < DEG ? 2 : 0) + rndint(2);
            if (sc > bestsc) { bestsc = sc; best = s; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        const uint64_t *bs = B + (size_t)best * W;
        for (int w = 0; w < W; w++) cov[w] |= bs[w];
    }
    int x = N;
    N++;
    side[x] = sx;
    dg[x] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (dg[s] >= DEG) {
            int t = adj[s][rndint(dg[s])];
            int k = find_edge(s, t);
            if (k >= 0) remove_edge(k);
        }
        if (dg[s] < DEG) add_cross(x, s);
    }
}

/* Remove k random vertices and relabel the rest. */
static void kill_vertices(int k) {
    static int dead[MAXN], mp[MAXN], ns[MAXN];
    for (int v = 0; v < N; v++) dead[v] = 0;
    int kills = 0;
    for (int t = 0; t < k; t++) {
        if (N - kills <= 2 * DEG + 2) break;
        int v = rndint(N);
        if (!dead[v]) { dead[v] = 1; kills++; }
    }
    int m = 0;
    for (int v = 0; v < N; v++) {
        if (dead[v]) mp[v] = -1;
        else { mp[v] = m; ns[m] = side[v]; m++; }
    }
    int ne = 0;
    for (int i = 0; i < nE; i++) {
        int a = mp[eu[i]], b = mp[ev[i]];
        if (a >= 0 && b >= 0) { eu[ne] = a; ev[ne] = b; ne++; }
    }
    nE = ne;
    N = m;
    for (int v = 0; v < N; v++) side[v] = ns[v];
}

/* Metropolis anneal on double-edge switches minimising bad pairs. */
static long long anneal(long long cost, int iters, double T, double tlimit) {
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 63) == 0 && elapsed() > tlimit) break;
        if (!propose_switch()) continue;
        long long nc = bad_pairs();
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = nc;
        else undo_switch();
    }
    return cost;
}

static void save_cur(void) {
    SV_N = N; SV_nE = nE;
    memcpy(SV_eu, eu, sizeof(int) * (size_t)nE);
    memcpy(SV_ev, ev, sizeof(int) * (size_t)nE);
    memcpy(SV_side, side, sizeof(int) * (size_t)N);
}

static int restore_cur(void) {
    N = SV_N; nE = SV_nE;
    memcpy(eu, SV_eu, sizeof(int) * (size_t)nE);
    memcpy(ev, SV_ev, sizeof(int) * (size_t)nE);
    memcpy(side, SV_side, sizeof(int) * (size_t)N);
    return rebuild_adj();
}

static void save_best(void) {
    BS_N = N; BS_nE = nE;
    memcpy(BS_eu, eu, sizeof(int) * (size_t)nE);
    memcpy(BS_ev, ev, sizeof(int) * (size_t)nE);
    memcpy(BS_side, side, sizeof(int) * (size_t)N);
}

static void load_best(void) {
    N = BS_N; nE = BS_nE;
    memcpy(eu, BS_eu, sizeof(int) * (size_t)nE);
    memcpy(ev, BS_ev, sizeof(int) * (size_t)nE);
    memcpy(side, BS_side, sizeof(int) * (size_t)N);
    rebuild_adj();
}

/* Fallback: K_{d,d}, valid for diameter >= 2. */
static void set_complete(void) {
    N = 2 * DEG;
    nE = 0;
    for (int v = 0; v < N; v++) side[v] = (v < DEG) ? 0 : 1;
    for (int a = 0; a < DEG; a++)
        for (int b = 0; b < DEG; b++) {
            eu[nE] = a; ev[nE] = DEG + b; nE++;
        }
    rebuild_adj();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double TL = atof(argv[4]);
    rng_state = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rng_state == 0) rng_state = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (DEG < 1 || DEG > MAXD || DIAM < 1) { printf("0 0\n"); return 0; }
    if (DIAM == 1) { printf("2 1\n0 1\n"); return 0; }

    /* Load start graph. */
    int n = 0, m = 0;
    int ok = 0;
    if (scanf("%d %d", &n, &m) == 2 && n >= 1 && n <= MAXN - 256 && m >= 0) ok = 1;
    if (ok) {
        int raw = 0;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
            if (raw >= MAXE) continue;
            eu[raw] = u; ev[raw] = v; raw++;
        }
        N = n;
        for (int v = 0; v < N; v++) dg[v] = 0;
        nE = 0;
        for (int i = 0; i < raw; i++) {
            int a = eu[i], b = ev[i];
            if (dg[a] >= DEG || dg[b] >= DEG || has_edge(a, b)) continue;
            adj[a][dg[a]++] = b;
            adj[b][dg[b]++] = a;
            eu[nE] = a; ev[nE] = b; nE++;
        }
        static int qu[MAXN];
        for (int v = 0; v < N; v++) side[v] = -1;
        int bip = 1;
        for (int s = 0; s < N && bip; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            qu[qt++] = s;
            while (qh < qt && bip) {
                int u = qu[qh++];
                for (int i = 0; i < dg[u]; i++) {
                    int w = adj[u][i];
                    if (side[w] < 0) { side[w] = 1 - side[u]; qu[qt++] = w; }
                    else if (side[w] == side[u]) { bip = 0; break; }
                }
            }
        }
        if (bip) {
            for (int i = 0; i < nE; i++) {
                if (side[eu[i]] == 1) { int t = eu[i]; eu[i] = ev[i]; ev[i] = t; }
            }
            ok = rebuild_adj();
        } else {
            ok = 0;
        }
    }
    if (!ok) set_complete();

    long long cost = bad_pairs();
    if (cost > 0) {
        fill_edges();
        rebuild_adj();
        cost = bad_pairs();
        if (cost > 0) cost = anneal(cost, 20000, 0.5, TL * 0.3);
    }
    if (cost != 0) set_complete();

    save_best();

    static const double temps[3] = {0.3, 0.6, 1.0};
    while (elapsed() < TL) {
        save_cur();
        rebuild_adj();
        if (rndint(10) < 8) grow_vertex();
        else kill_vertices(1 + rndint(3));
        if (!rebuild_adj()) { restore_cur(); continue; }
        fill_edges();
        if (!rebuild_adj()) { restore_cur(); continue; }
        cost = bad_pairs();
        cost = anneal(cost, ANNEAL_ITERS, temps[rndint(3)], TL);
        if (cost == 0) {
            if (N > BS_N) save_best();
            else if (N < BS_N - 3) load_best();
        } else {
            restore_cur();
        }
    }

    printf("%d %d\n", BS_N, BS_nE);
    for (int i = 0; i < BS_nE; i++) printf("%d %d\n", BS_eu[i], BS_ev[i]);
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=200):
    """Add vertices whose neighbourhoods are cover sets of the opposite side."""
    if D < 2:
        return n, list(edges)
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
    """Join deficient opposite-side vertices in random order (only helps distances)."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Cover-vertex growth alternated with saturation."""
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
    """One randomized pipeline mixing twin duplication, saturation and cover growth."""
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
# Driver. Python builds structured candidates; C anneals a grow/kill search
# from the best one. Every result is checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    span = end - start
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    def at(f):
        return start + f * span

    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d} fallback
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base (W(q) for D >= 4, PG(2,q) for D = 3), grown.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)

    if best_n >= bound:
        return best_n, list(best_e)

    # Phase B: randomized twin / saturation / growth trials.
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end and best_n < bound:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if best_n >= bound:
        return best_n, list(best_e)

    # Phase C: C annealing search (grow, kill, repair) from the best graph.
    if D >= 2:
        remaining = end - time.monotonic() - 1.0
        if remaining > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=remaining + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)

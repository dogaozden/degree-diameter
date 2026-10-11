import random
import time

import lib

# Bold change for the D = 3 targets: start from the Araujo-Pardo-Lopez record graph
# (order 2(q^2+q+5), degree q+2 with q = d-2 a prime power) instead of a projective
# plane, then let a C simulated-annealing engine try to add vertices. The engine works
# on the whole graph: it grows by one vertex at a time and repairs bad pairs with
# degree-preserving edge switches, endpoint moves and free edge additions. The best
# valid graph is always kept. Every candidate is checked with lib.is_valid, and the
# Python construction is the fallback if the C run fails.

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXD 64
#define MAXE 32768

static int N, Dd, Dist;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char adjm[MAXN][MAXN];
static int col[MAXN];
static int EU[MAXE], EV[MAXE], NE;
static int BEU[MAXE], BEV[MAXE], bestN, bestNE;
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static uint64_t rs;
static double budget;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void nb_remove(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) { nb[a][k] = nb[a][deg[a] - 1]; deg[a]--; return; }
    }
}

static void add_pair(int a, int b) {
    if (col[a] != 0) { int t = a; a = b; b = t; }
    EU[NE] = a; EV[NE] = b; NE++;
    adjm[a][b] = 1; adjm[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_pair(int a, int b) {
    for (int i = 0; i < NE; i++) {
        if ((EU[i] == a && EV[i] == b) || (EU[i] == b && EV[i] == a)) {
            EU[i] = EU[NE - 1]; EV[i] = EV[NE - 1]; NE--; break;
        }
    }
    adjm[a][b] = 0; adjm[b][a] = 0;
    nb_remove(a, b); nb_remove(b, a);
}

/* number of unordered pairs at distance > Dist */
static long cost(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[v * W + (v >> 6)] |= (uint64_t)1 << (v & 63);
    for (int step = 0; step < Dist; step++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + v * W;
            const uint64_t *c0 = cur + v * W;
            for (int w = 0; w < W; w++) o[w] = c0[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *cu = cur + nb[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
            for (int w = 0; w < W; w++) if (o[w] != c0[w]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v * W + w]);
        bad += N - c;
    }
    return bad / 2;
}

typedef struct { int nr, na; int ra[2], rb[2], aa[2], ab[2]; } Move;

static int pick_vertex(int c) {
    for (int t = 0; t < 40; t++) {
        int v = rndi(N);
        if (col[v] == c && deg[v] < Dd) return v;
    }
    return -1;
}

static int gen_move(Move *m) {
    m->nr = 0; m->na = 0;
    double r = rndu();
    if (r < 0.4) {
        /* degree-preserving edge switch */
        if (NE < 2) return 0;
        int i = rndi(NE), j = rndi(NE);
        if (i == j) return 0;
        int a = EU[i], b = EV[i], c = EU[j], e = EV[j];
        if (a == c || b == e) return 0;
        if (adjm[a][e] || adjm[c][b]) return 0;
        m->nr = 2; m->ra[0] = a; m->rb[0] = b; m->ra[1] = c; m->rb[1] = e;
        m->na = 2; m->aa[0] = a; m->ab[0] = e; m->aa[1] = c; m->ab[1] = b;
        return 1;
    }
    if (r < 0.85) {
        /* move one endpoint of an edge to a vertex with spare degree */
        if (NE < 1) return 0;
        int i = rndi(NE);
        int a = EU[i], b = EV[i];
        if (rndi(2) == 0) {
            int e = pick_vertex(1);
            if (e < 0 || e == b || adjm[a][e]) return 0;
            m->nr = 1; m->ra[0] = a; m->rb[0] = b;
            m->na = 1; m->aa[0] = a; m->ab[0] = e;
        } else {
            int f = pick_vertex(0);
            if (f < 0 || f == a || adjm[f][b]) return 0;
            m->nr = 1; m->ra[0] = a; m->rb[0] = b;
            m->na = 1; m->aa[0] = f; m->ab[0] = b;
        }
        return 1;
    }
    /* free edge addition between spare-degree vertices */
    int u = pick_vertex(0), v = pick_vertex(1);
    if (u < 0 || v < 0 || adjm[u][v]) return 0;
    m->na = 1; m->aa[0] = u; m->ab[0] = v;
    return 1;
}

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_pair(m->ra[i], m->rb[i]);
    for (int i = 0; i < m->na; i++) add_pair(m->aa[i], m->ab[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_pair(m->aa[i], m->ab[i]);
    for (int i = 0; i < m->nr; i++) add_pair(m->ra[i], m->rb[i]);
}

static void add_vertex(void) {
    int x = N;
    N++;
    col[x] = rndi(2);
    deg[x] = 0;
    int order[MAXN], k = 0;
    for (int v = 0; v < x; v++) if (col[v] != col[x]) order[k++] = v;
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = order[i]; order[i] = order[j]; order[j] = t;
    }
    for (int i = 0; i < k && deg[x] < Dd; i++) {
        int v = order[i];
        if (deg[v] < Dd && !adjm[x][v]) add_pair(x, v);
    }
}

static void save_best(void) {
    bestN = N; bestNE = NE;
    memcpy(BEU, EU, sizeof(int) * (size_t)NE);
    memcpy(BEV, EV, sizeof(int) * (size_t)NE);
}

static void print_best(void) {
    printf("%d %d\n", bestN, bestNE);
    for (int i = 0; i < bestNE; i++) printf("%d %d\n", BEU[i], BEV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    Dd = d; Dist = D;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 >= MAXN - 2 || m0 < 0 ||
        m0 > MAXE || d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    int *RU = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *RV = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!RU || !RV) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &RU[i], &RV[i]) != 2) { printf("0 0\n"); return 0; }
        if (RU[i] < 0 || RU[i] >= n0 || RV[i] < 0 || RV[i] >= n0) { printf("0 0\n"); return 0; }
    }

    /* 2-colour the input (bipartite by promise) */
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < m0; i++) {
                int u = RU[i], v = RV[i];
                if (col[u] >= 0 && col[v] < 0) { col[v] = 1 - col[u]; changed = 1; }
                else if (col[v] >= 0 && col[u] < 0) { col[u] = 1 - col[v]; changed = 1; }
            }
        }
    }

    N = n0; NE = 0;
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u = RU[i], v = RV[i];
        if (u == v || col[u] == col[v] || adjm[u][v] || deg[u] >= Dd || deg[v] >= Dd) ok = 0;
        else add_pair(u, v);
    }
    if (!ok || cost() != 0) { printf("0 0\n"); return 0; }

    long cur = cost();
    long it = 0;
    for (;;) {
        if (cur == 0) {
            save_best();
            if (N >= MAXN - 2 || now() >= budget) break;
            add_vertex();
            cur = cost();
            continue;
        }
        if (now() >= budget) break;
        it++;
        double T = 2.0 * (1.0 - (double)(it % 4000) / 4000.0) + 0.1;
        Move mv;
        if (!gen_move(&mv)) continue;
        apply_move(&mv);
        long c = cost();
        long delta = c - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur = c;
        else undo_move(&mv);
    }
    print_best();
    return 0;
}
"""


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
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


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved.
    """
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree.

    Extra edges only shorten distances and keep the graph bipartite, so the diameter
    bound and bipartiteness are preserved.
    """
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- starting graphs

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _al_base(d, D):
    """Araujo-Pardo-Lopez graph for degree d = q+2 (q a prime power >= 3), diameter 3."""
    q = d - 2
    if D != 3 or q < 3 or not lib.is_prime_power(q):
        return None
    try:
        n, e = lib.araujo_lopez_graph(q)
    except Exception:
        return None
    return (n, e) if lib.is_valid(n, e, d, D) else None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        pg = lib.projective_plane_incidence(d - 1)   # Moore-extremal, nothing to improve
        if lib.is_valid(pg[0], pg[1], d, D):
            return pg

    # Fallback candidates, always valid.
    cands = [lib.haar_graph(d, range(d))]

    # Starting graphs: the record construction first, then the projective plane.
    bases = []
    al = _al_base(d, D)
    if al is not None:
        bases.append(al)
    if d >= 3:
        pg = _pg_base(d)
        if pg is not None:
            bases.append(pg)

    pre_end = time.monotonic() + min(2.0, 0.05 * time_limit)
    for g in bases:
        cands.append(g)
        aug = _augment(g[0], g[1], d, seed)
        cands.append(aug)
        cands.append(_extend(aug[0], aug[1], d, D, rng,
                             min(pre_end, time.monotonic() + 0.8)))

    best = _finish(cands, d, D)

    # C search: grow from the best valid start. Stop well before time_limit.
    remaining = time_limit - (time.monotonic() - t0)
    cbudget = min(0.85 * remaining, remaining - 7.0)
    if cbudget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget, 2)],
                             stdin_graph=best, timeout=remaining - 2.5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass
    return best

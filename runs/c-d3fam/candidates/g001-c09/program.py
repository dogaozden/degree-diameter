import time

import lib

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 40
#define MAXW ((MAXN + 63) / 64)

static int D, DEG, n, W;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static uint64_t ball[MAXN][MAXW], nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int bu[MAXN * MAXDEG], bv[MAXN * MAXDEG];
static int bestn = -1, bestm = 0;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (nb[u][i] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) { nb[u][deg[u]++] = v; nb[v][deg[v]++] = u; }
static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
}
static void remove_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* number of ordered pairs (v,w) with dist(v,w) > D */
static long cost(void) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(ball[v], 0, sizeof(uint64_t) * W);
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = ball[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) ball[v][w] = nxt[v][w];
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(ball[v][w]);
        bad += n - c;
    }
    return bad;
}

static void save_best(void) {
    bestn = n;
    bestm = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] != 0) continue;
        for (int i = 0; i < deg[v]; i++) {
            bu[bestm] = v;
            bv[bestm] = nb[v][i];
            bestm++;
        }
    }
}

static void grow(void) {
    side[n] = 0; side[n + 1] = 1;
    deg[n] = 0; deg[n + 1] = 0;
    n += 2;
}

typedef struct { int type, a, b, c, d; } Mv;

static void apply(const Mv *m, int undo) {
    if (m->type == 0) {
        if (!undo) { remove_edge(m->a, m->b); add_edge(m->a, m->c); }
        else       { remove_edge(m->a, m->c); add_edge(m->a, m->b); }
    } else if (m->type == 1) {
        if (!undo) {
            remove_edge(m->a, m->b); remove_edge(m->c, m->d);
            add_edge(m->a, m->d); add_edge(m->c, m->b);
        } else {
            remove_edge(m->a, m->d); remove_edge(m->c, m->b);
            add_edge(m->a, m->b); add_edge(m->c, m->d);
        }
    } else {
        if (!undo) add_edge(m->a, m->b);
        else remove_edge(m->a, m->b);
    }
}

static int propose(Mv *m) {
    int r = rndi(100);
    if (r < 40) {
        int x = rndi(n);
        if (!deg[x]) return 0;
        int y = nb[x][rndi(deg[x])];
        int keep, old;
        if (rndi(2)) { keep = x; old = y; } else { keep = y; old = x; }
        int z = -1;
        for (int t = 0; t < 40; t++) {
            int c = rndi(n);
            if (side[c] == side[old] && c != old && deg[c] < DEG && !has_edge(keep, c)) { z = c; break; }
        }
        if (z < 0) return 0;
        m->type = 0; m->a = keep; m->b = old; m->c = z; m->d = 0;
        return 1;
    } else if (r < 75) {
        int x = rndi(n);
        if (!deg[x]) return 0;
        int y = nb[x][rndi(deg[x])];
        int x2 = rndi(n);
        if (!deg[x2]) return 0;
        int y2 = nb[x2][rndi(deg[x2])];
        int a1, b1, a2, b2;
        if (side[x] == 0) { a1 = x; b1 = y; } else { a1 = y; b1 = x; }
        if (side[x2] == 0) { a2 = x2; b2 = y2; } else { a2 = y2; b2 = x2; }
        if (a1 == a2 || b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) return 0;
        m->type = 1; m->a = a1; m->b = b1; m->c = a2; m->d = b2;
        return 1;
    } else {
        int u = rndi(n), v = rndi(n);
        if (side[u] == side[v] || deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) return 0;
        if (side[u] == 1) { int t = u; u = v; v = t; }
        m->type = 2; m->a = u; m->b = v; m->c = 0; m->d = 0;
        return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)(atoll(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);

    int m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 1 || n > MAXN - 4 || m < 0 || DEG < 1 || DEG >= MAXDEG) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* 2-colour; reject non-bipartite input */
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[u][i];
                if (side[w] < 0) { side[w] = 1 - side[u]; q[t++] = w; }
                else if (side[w] == side[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    long cur = cost();
    if (cur == 0) {
        save_best();
        if (n + 2 <= MAXN - 2) { grow(); cur = cost(); }
    }

    const double T0 = 2.5;
    const long PHASE = 30000;
    long it = 0;
    clock_t c0 = clock();
    while (1) {
        if ((it & 127) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > budget) break;
        it++;
        double frac = (double)(it % PHASE) / (double)PHASE;
        double T = T0 * (0.03 + 0.97 * (1.0 - frac));
        Mv mv;
        if (!propose(&mv)) continue;
        apply(&mv, 0);
        long c2 = cost();
        long delta = c2 - cur;
        if (delta <= 0 || rndf() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            apply(&mv, 1);
            continue;
        }
        if (cur == 0) {
            save_best();
            if (n + 2 <= MAXN - 2) { grow(); cur = cost(); }
        }
    }

    if (bestn < 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestn, bestm);
    for (int i = 0; i < bestm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
'''


# ---------------------------------------------------------------- constructions

def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _al_base(d):
    """Araujo-Pardo & Lopez graph of degree d when d-2 is a prime power >= 3 (record for D = 3)."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except ValueError:
        return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    cands = [lib.haar_graph(d, range(d))]
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            cands.append(base)
            if D == 3 and lib.is_prime_power(d - 1):
                return _finish(cands, d, D)  # Moore-extremal, nothing to improve
    if D == 3:
        al = _al_base(d)
        if al is not None:
            cands.append(al)

    best = _finish(cands, d, D)

    # Fixed-degree annealing with vertex insertion, started from the best valid graph.
    # Stays valid if anything fails: the fallback `best` is returned.
    elapsed = time.monotonic() - start
    budget_c = max(1.0, 0.6 * time_limit - 2.0 - elapsed)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget_c, 2)],
                        stdin_graph=best, timeout=0.85 * time_limit)
        n2, e2 = lib.parse_graph_text(out)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    return best

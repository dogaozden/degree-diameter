"""Lift annealing over wide base multigraphs (p up to 6 fibres per side) with metacyclic groups.

Different search space from the earlier bi-Cayley version. The base multigraph is a d-regular
bipartite multigraph on p + p vertices, and it is rewired during annealing: dart endpoints are
swapped, and voltages are changed. The lift has 2pN vertices. Diameter is checked exactly with
BFS from one identity per fibre (2p sources), which is exact because left multiplication acts
transitively on each fibre. Each annealing run minimises the number of pairs left outside
distance D. Successes are validated with the full bitset check before they are accepted.

Targets: the record plus 2 is aimed at directly half of the time. The other half climbs in
adaptive steps from the current best. The start is the best algebraic graph (PG(2,q), W(q),
Araujo-Pardo-Lopez, or K_{d,d}), and it is returned unchanged if the search finds nothing valid
and larger.
"""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 16
#define MAXP 6
#define MAXDART (MAXP * MAXD)
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long MOORE;
static long target_n = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void add_edge(Graph *g, int u, int v) {
    if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return;
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (bitset ball expansion). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------- metacyclic group Z_m x| Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e) ---------- */
static int Gm, Gk, Gr, Ncur;
static int rp[MAXN];

static int gmul(int x, int y) {
    int a = x / Gk, b = x % Gk, c = y / Gk, e = y % Gk;
    return (int)(((long)a + (long)rp[b] * c) % Gm) * Gk + (b + e) % Gk;
}

static void setup_group(int N) {
    Ncur = N;
    int divs[512], cnt = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0 && cnt < 512) divs[cnt++] = m;
    int m = divs[rndint(cnt)];
    Gm = m;
    Gk = N / m;
    int r = 0;
    if (m > 1) {
        r = 1;
        for (int tr = 0; tr < 300; tr++) {
            int c = 1 + rndint(m - 1);
            if (gcd(c, m) == 1 && powmod(c, Gk, m) == 1) { r = c; break; }
        }
    }
    Gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < Gk; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

/* ---------- lift state: base darts t = (dA[t], dB[t], voltage gv[t]) ---------- */
static int dA[MAXDART], dB[MAXDART], gv[MAXDART], posB[MAXDART];
static int fibA[MAXP][MAXD], fibB[MAXP][MAXD];
static int rm[MAXDART][MAXN], rmi[MAXDART][MAXN];
static int vis[MAXN], lev[MAXN], qbuf[MAXN];
static int stampc = 0;

/* Set voltage g on dart t and refresh right-multiplication tables for g and g^{-1}. */
static void set_volt(int t, int g) {
    gv[t] = g;
    int a = g / Gk, b = g % Gk;
    int bp = (Gk - b) % Gk;
    long ai = (Gm - ((long)a * rp[bp]) % Gm) % Gm;
    int gi = (int)ai * Gk + bp;
    for (int x = 0; x < Ncur; x++) {
        rm[t][x] = gmul(x, g);
        rmi[t][x] = gmul(x, gi);
    }
}

static int clash_g(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && gv[s] >= 0 && gv[s] == g && dA[s] == dA[t] && dB[s] == dB[t]) return 1;
    return 0;
}

/* Exchange the B-endpoints of darts t1 and t2 (self-inverse). */
static void do_swap(int t1, int t2) {
    int j1 = dB[t1], j2 = dB[t2];
    int p1 = posB[t1], p2 = posB[t2];
    fibB[j1][p1] = t2;
    fibB[j2][p2] = t1;
    posB[t1] = p2;
    posB[t2] = p1;
    dB[t1] = j2;
    dB[t2] = j1;
}

static int init_state(int p) {
    int nd = p * d;
    for (int i = 0; i < p; i++)
        for (int s = 0; s < d; s++) fibA[i][s] = s * p + i;
    int cnt[MAXP];
    for (int j = 0; j < MAXP; j++) cnt[j] = 0;
    for (int t = 0; t < nd; t++) gv[t] = -1;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < p; i++) {
            int t = s * p + i;
            dA[t] = i;
            dB[t] = perm[i];
            fibB[perm[i]][cnt[perm[i]]] = t;
            posB[t] = cnt[perm[i]];
            cnt[perm[i]]++;
        }
    }
    for (int t = 0; t < nd; t++) {
        int g = 0, tries = 0;
        do {
            g = rndint(Ncur);
            tries++;
        } while (clash_g(t, g, nd) && tries < 100000);
        if (clash_g(t, g, nd)) return 0;
        set_volt(t, g);
    }
    return 1;
}

/* BFS from src; returns the number of vertices within distance D (including src). */
static int bfs_reach(int src, int p) {
    int N = Ncur;
    int pN = p * N;
    stampc++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    vis[src] = stampc;
    lev[src] = 0;
    while (head < tail) {
        int v = qbuf[head++];
        int lv = lev[v];
        if (lv >= D) continue;
        int f = v / N, x = v - f * N;
        if (v < pN) {
            for (int s = 0; s < d; s++) {
                int t = fibA[f][s];
                int w = (p + dB[t]) * N + rm[t][x];
                if (vis[w] != stampc) {
                    vis[w] = stampc;
                    lev[w] = lv + 1;
                    qbuf[tail++] = w;
                }
            }
        } else {
            int j = f - p;
            for (int s = 0; s < d; s++) {
                int t = fibB[j][s];
                int w = dA[t] * N + rmi[t][x];
                if (vis[w] != stampc) {
                    vis[w] = stampc;
                    lev[w] = lv + 1;
                    qbuf[tail++] = w;
                }
            }
        }
    }
    return tail;
}

/* Energy: pairs at distance > D from the 2p fibre identities (zero iff the lift has diameter <= D). */
static long energy(int p) {
    long E = 0;
    int nv = 2 * p * Ncur;
    for (int f = 0; f < 2 * p; f++) E += nv - bfs_reach(f * Ncur, p);
    return E;
}

static long anneal(int p, double run_until) {
    int nd = p * d;
    double t0 = now();
    double span = run_until - t0;
    if (span < 1e-3) span = 1e-3;
    long E = energy(p);
    double T = 2.0;
    for (long it = 0; E > 0; it++) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn >= run_until) break;
            double f = (tn - t0) / span;
            T = 0.05 + 2.0 * (1.0 - f);
        }
        if (rndint(2) == 0) {
            int t = rndint(nd);
            int g = rndint(Ncur);
            if (g == gv[t] || clash_g(t, g, nd)) continue;
            int old = gv[t];
            set_volt(t, g);
            long En = energy(p);
            if (En <= E || rnd01() < exp((double)(E - En) / T)) E = En;
            else set_volt(t, old);
        } else {
            int t1 = rndint(nd), t2 = rndint(nd);
            if (t1 == t2 || dB[t1] == dB[t2]) continue;
            do_swap(t1, t2);
            if (clash_g(t1, gv[t1], nd) || clash_g(t2, gv[t2], nd)) {
                do_swap(t1, t2);
                continue;
            }
            long En = energy(p);
            if (En <= E || rnd01() < exp((double)(E - En) / T)) E = En;
            else do_swap(t1, t2);
        }
    }
    return E;
}

static void build_graph(Graph *g, int p) {
    int N = Ncur, nd = p * d;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dA[t] * N + x, (p + dB[t]) * N + rm[t][x]);
}

static int attempt(Graph *best, int p, long N, double until) {
    static Graph cand;
    while (now() < until) {
        setup_group((int)N);
        if (!init_state(p)) continue;
        double rem = until - now();
        double run = rem * 0.5;
        if (run < 0.3) run = rem;
        long E = anneal(p, now() + run);
        if (E == 0) {
            build_graph(&cand, p);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                return 1;
            }
        }
    }
    return 0;
}

static void search(Graph *best, double until) {
    long step = 2;
    while (now() < until) {
        if (best->n + 2 > MOORE) return;
        int p = 1 + rndint(MAXP);
        int tgt = (target_n > best->n) && rndint(2) == 0;
        long goal = tgt ? target_n : best->n + step;
        long N = (goal + 2L * p - 1) / (2L * p);
        if (rndint(3) == 0) N += 1 + rndint(2);
        if (N < d) N = d;
        if (2L * p * N > MOORE || 2L * p * N > MAXN) {
            if (!tgt && step > 2) step = 2;
            continue;
        }
        double left = until - now();
        double sl;
        if (tgt) {
            sl = left / 4;
            if (sl > 8.0) sl = 8.0;
        } else {
            sl = left / 6;
            if (sl > 3.0) sl = 3.0;
        }
        if (sl < 0.5) sl = left;
        int ok = attempt(best, p, N, now() + sl);
        if (!tgt) {
            if (ok) { if (step < 256) step *= 2; }
            else if (step > 2) step /= 2;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    double t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    MOORE = moore_bound();
    static Graph best;
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);
    if (best.n + 2 <= MOORE && now() < t_end) search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Best known orders. The C search targets record + 2.
RECORDS = {(3, 3): 14, (4, 8): 2184}


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    rec = RECORDS.get((d, D), 0)
    target = rec + 2 if rec else 0
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), target],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

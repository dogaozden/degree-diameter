"""Combined program: known constructions from Python, then one C engine that runs a
bi-Cayley lift search (voltage lifts over semidirect products Z_m x| Z_k, annealed on
block reachability) and grows from the best valid graph found so far."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search for bipartite degree-diameter graphs.
 * Usage: prog d D seed time_limit < start_graph
 * Model: group H = Z_m x|_r Z_k2 of order G, k A-blocks and k B-blocks.
 * Layer l maps A-block i to B-block lay[l][i] with voltage S[l][i]:
 *   A(i,g) ~ B(j, g*s). Left multiplication is an automorphism, so the diameter
 * is <= D iff every vertex is within D of every block representative.
 * Cost = unreached (vertex, rep) pairs + PEN * duplicate darts.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define MAXG (MAXN / 2)
#define PEN 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k2, r, G;
    int rp[MAXG];
    int ga[MAXG], gb[MAXG];
} Grp;

typedef struct {
    int k, G;
    int lay[MAXD][MAXK];
    int S[MAXD][MAXK];
} State;

static int d, D;
static double t_end;
static Graph best;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int nbr[MAXD][MAXN];
static unsigned char rch[MAXN], rtmp[MAXN];
static int RT[MAXG], RE[MAXG];

/* ---------------------------------------------------------------- utilities */

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

/* ---------------------------------------------------------- graph checks */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* Number of unordered pairs at distance > D. */
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
    static int queue[MAXN];
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static void group_prep(Grp *Gp) {
    Gp->rp[0] = 1 % Gp->m;
    for (int b = 1; b < Gp->k2; b++)
        Gp->rp[b] = (int)((long)Gp->rp[b - 1] * Gp->r % Gp->m);
    for (int x = 0; x < Gp->G; x++) {
        Gp->ga[x] = x / Gp->k2;
        Gp->gb[x] = x % Gp->k2;
    }
}

static int random_group(int N, Grp *Gp) {
    long count = 0;
    int ok = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            count++;
            if ((long)(rnd() % (uint64_t)count) == 0) {
                Gp->m = m;
                Gp->k2 = k2;
                Gp->r = r;
                ok = 1;
            }
        }
    }
    if (!ok) return 0;
    Gp->G = N;
    group_prep(Gp);
    return 1;
}

static int ginv(const Grp *Gp, int x) {
    int a = Gp->ga[x], b = Gp->gb[x];
    int nb = (Gp->k2 - b) % Gp->k2;
    long p = (long)Gp->rp[nb] * a % Gp->m;
    int ia = p ? Gp->m - (int)p : 0;
    return ia * Gp->k2 + nb;
}

/* Right multiplication by s: T[b] = r^b * sa mod m, E[b] = (b + sb) mod k2. */
static void right_tables(const Grp *Gp, int s, int *T, int *E) {
    int sa = s / Gp->k2, sb = s % Gp->k2;
    for (int b = 0; b < Gp->k2; b++) {
        T[b] = (int)((long)Gp->rp[b] * sa % Gp->m);
        E[b] = (b + sb) % Gp->k2;
    }
}

/* ---------------------------------------------------------- bi-Cayley lifts */

static void random_state(State *st, int k, int G) {
    st->k = k;
    st->G = G;
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k; i++) {
            st->lay[l][i] = p[i];
            st->S[l][i] = rndint(G);
        }
    }
}

/* nbr[l][v]: A-vertices are 0..kG-1, B-vertices kG..2kG-1. */
static void build_nbr(const State *st, const Grp *Gp) {
    int k = st->k, G = st->G, m = Gp->m, k2 = Gp->k2;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = st->lay[l][i];
            int s = st->S[l][i];
            int si = ginv(Gp, s);
            right_tables(Gp, s, RT, RE);
            for (int g = 0; g < G; g++) {
                int b = Gp->gb[g];
                int x = Gp->ga[g] + RT[b];
                if (x >= m) x -= m;
                nbr[l][i * G + g] = (k + j) * G + x * k2 + RE[b];
            }
            right_tables(Gp, si, RT, RE);
            for (int h = 0; h < G; h++) {
                int b = Gp->gb[h];
                int x = Gp->ga[h] + RT[b];
                if (x >= m) x -= m;
                nbr[l][(k + j) * G + h] = i * G + x * k2 + RE[b];
            }
        }
    }
}

static long eval_state(const State *st, const Grp *Gp) {
    int k = st->k, G = st->G, N = 2 * k * G;
    build_nbr(st, Gp);
    memset(rch, 0, (size_t)N);
    for (int b = 0; b < 2 * k; b++) rch[b * G] = (unsigned char)(1 << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            unsigned char x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nbr[l][v]];
            rtmp[v] = x;
            changed |= (x != rch[v]);
        }
        memcpy(rch, rtmp, (size_t)N);
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += 2 * k - __builtin_popcount(rch[v]);

    long dup = 0;
    int M = d * k;
    for (int a = 0; a < M; a++) {
        int li = a / k, ii = a % k;
        for (int c = 0; c < a; c++) {
            int lc = c / k, ic = c % k;
            if (ii == ic && st->lay[li][ii] == st->lay[lc][ic] && st->S[li][ii] == st->S[lc][ic])
                dup++;
        }
    }
    return cost + PEN * dup;
}

static int anneal(State *st, const Grp *Gp, long iters, long patience, double deadline) {
    State cur = *st, saved;
    int k = cur.k, G = cur.G, N = 2 * k * G, full = (1 << (2 * k)) - 1;
    long cost = eval_state(&cur, Gp);
    long best_cost = cost, last = 0;
    double c0 = cost > 1 ? (double)cost : 1.0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 15) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / iters) + 0.3;
        saved = cur;
        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = cur.lay[l][i1];
            cur.lay[l][i1] = cur.lay[l][i2];
            cur.lay[l][i2] = tmp;
        } else {
            int l = rndint(d), i = rndint(k);
            if (rnd01() < 0.4) {
                for (int tries = 0; tries < 30; tries++) {
                    int v = rndint(N);
                    if (rch[v] != full) {
                        int b = v / G;
                        if (b < k) i = b;
                        else {
                            int j = b - k;
                            for (int ii = 0; ii < k; ii++)
                                if (cur.lay[l][ii] == j) { i = ii; break; }
                        }
                        break;
                    }
                }
            }
            int s = rndint(G);
            if (s == cur.S[l][i]) continue;
            cur.S[l][i] = s;
        }
        long c2 = eval_state(&cur, Gp);
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
            cost = c2;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            cur = saved;
        }
    }
    *st = cur;
    return cost == 0;
}

/* Expand a valid bi-Cayley state into an explicit graph. */
static int expand(const State *st, const Grp *Gp, Graph *g) {
    int k = st->k, G = st->G, N = 2 * k * G;
    if (N > MAXN) return 0;
    build_nbr(st, Gp);
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int l = 0; l < d; l++)
        for (int u = 0; u < k * G; u++) {
            int v = nbr[l][u];
            if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
            add_edge(g, u, v);
        }
    return 1;
}

static int pick_k(const double *wins, const double *trials) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bs = -1;
    for (int k = 1; k <= MAXK; k++) {
        double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.05 * rnd01();
        if (sc > bs) { bs = sc; bk = k; }
    }
    return bk;
}

static void search(double until) {
    static State st;
    static Grp Gp;
    static Graph cand;
    double wins[MAXK + 1] = {0}, trials[MAXK + 1] = {0};
    double step = best.n / 40.0;
    if (step < 2) step = 2;
    while (now() < until) {
        if (best.n + 2 > MAXN || best.n + 2 > moore_bound()) break;
        int k = pick_k(wins, trials);
        long target = best.n + (long)step;
        long G = (target + 2L * k - 1) / (2L * k);
        if (2L * k * G <= best.n) G = best.n / (2L * k) + 1;
        if (2L * k * G > MAXN) { step = 2; continue; }
        if (G < 2) G = 2;
        if (!random_group((int)G, &Gp)) continue;
        random_state(&st, k, (int)G);
        trials[k] += 1;
        double remain = until - now();
        double slice = remain / 4;
        if (slice < 3) slice = remain;
        int ok = anneal(&st, &Gp, 40000, 4000, now() + slice);
        if (ok && expand(&st, &Gp, &cand) && cand.n > best.n && is_valid(&cand)) {
            best = cand;
            wins[k] += 1;
            step = step * 1.3 + 2;
        } else {
            step *= 0.85;
            if (step < 2) step = 2;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("1 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    search(t_end);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _starts(d, D):
    """Known valid starting graphs for (d, D), as (n, edges) tuples."""
    out = []
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4 and d - 1 >= 2:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    best = lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 2:
        return best
    for cand in _starts(d, D):
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    if D == 3 and lib.is_prime_power(d - 1):    # Moore graph: optimal
        return best
    if d > 32:
        return best
    budget = 0.8 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best

"""Multi-orbit affine voltage lifts for the bipartite degree-diameter problem.

Construction: let G = F_q x| H be an affine group (H a subgroup of F_q^* of order c,
c >= 1), so |G| = N = q*c. Take K left orbits and K right orbits, each a copy of G.
The base structure has d layers. In layer t, left orbit i is joined to right orbit
sigma_t(i) through a dart with group label g_{t,i}, where sigma_t is a permutation of
{0..K-1}. The lift has vertices L_{i,x} and R_{j,y} and edges L_{i,x} ~ R_{j, x*g}.
Each vertex has degree d, the graph is bipartite, and it has 2KN vertices.

The parent is the K = 1 special case. For K >= 2 the family is genuinely different:
the base is a d-regular bipartite multigraph on K+K vertices with voltages in G.

Diameter: left multiplication by G is an automorphism that acts regularly on each
orbit. So it suffices to run BFS from one representative of each of the 2K orbits
and count unreached vertices. The cost is the total number of unreached vertices.
Search: iterated annealing over the group labels and the layer permutations. Each
round perturbs the incumbent and anneals from a lower temperature. Candidates
(K, q, c) are tried in ascending order of order 2KN, each with a time slice. The
largest success is returned.
Fallbacks: K_{d,d}, PG(2,q), Araujo-Pardo-Lopez graphs, and W(q) for D = 4. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine voltage lift search.
 * Usage: prog d D seed time_limit vlo vhi kmax   (stdin ignored)
 * Output: "V E" then E lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4096
#define MAXD 32
#define MAXK 4
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 16384

typedef struct { int K, q, p, k, c, N, V; } Cand;
typedef struct { int kind, t, i, j, val; } Move;

static int d, D, K;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, h_j = g^(j*(q-1)/c). Product:
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). The identity is code 0. */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */

/* Layer t, left orbit i: dart goes to right orbit PERM[t][i] with label GEL[t][i].
 * GFW[t][i][x] = x*g (right endpoint index), GBW[t][i][y] = y*g^-1 (left endpoint). */
static int PERM[MAXD][MAXK], IPERM[MAXD][MAXK], GEL[MAXD][MAXK];
static int GFW[MAXD][MAXK][MAXN], GBW[MAXD][MAXK][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_dart(int t, int i, int g) {
    GEL[t][i] = g;
    int gi = ginv(g);
    for (int x = 0; x < GN; x++) {
        GFW[t][i][x] = gmul(x, g);
        GBW[t][i][x] = gmul(x, gi);
    }
}

static void refresh_iperm(int t) {
    for (int i = 0; i < K; i++) IPERM[t][PERM[t][i]] = i;
}

static void rebuild_all(void) {
    for (int t = 0; t < d; t++) refresh_iperm(t);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) set_dart(t, i, GEL[t][i]);
}

/* Vertices: left (i,x) = i*N + x; right (j,y) = K*N + j*N + y. */
static int bfs_reach(int src) {
    int N = GN, base = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < base) {
                int i = v / N, x = v % N;
                for (int t = 0; t < d; t++) {
                    int u = base + PERM[t][i] * N + GFW[t][i][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int r = v - base, j = r / N, y = r % N;
                for (int t = 0; t < d; t++) {
                    int i = IPERM[t][j];
                    int u = i * N + GBW[t][i][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left-multiplication is an automorphism acting regularly on each orbit, so one BFS per
 * orbit representative decides the diameter. Cost = total unreached vertices. */
static long cover_cost(void) {
    int N = GN, V = 2 * K * N;
    long c = 0;
    for (int i = 0; i < K; i++) c += (long)(V - bfs_reach(i * N));
    for (int j = 0; j < K; j++) c += (long)(V - bfs_reach(K * N + j * N));
    return c;
}

/* Simple graph iff no two darts from the same left orbit share target and label. */
static int simple_ok(void) {
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++)
            for (int u = t + 1; u < d; u++)
                if (PERM[t][i] == PERM[u][i] && GEL[t][i] == GEL[u][i]) return 0;
    return 1;
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) PERM[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rndint(i + 1), tmp = PERM[t][i];
            PERM[t][i] = PERM[t][r];
            PERM[t][r] = tmp;
        }
        refresh_iperm(t);
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) {
            int g = 0;
            for (int tries = 0; tries < 100000; tries++) {
                g = rndint(GN);
                int ok = 1;
                for (int u = 0; u < t && ok; u++)
                    if (PERM[u][i] == PERM[t][i] && GEL[u][i] == g) ok = 0;
                if (ok) break;
            }
            set_dart(t, i, g);
        }
}

/* Moves: kind 0 changes one label; kind 1 swaps two targets within a layer.
 * do_move applied twice is the identity, so it also serves as undo. */
static int propose(Move *m) {
    if (K >= 2 && rndint(10) < 3) {
        m->kind = 1;
        m->t = rndint(d);
        m->i = rndint(K);
        m->j = rndint(K - 1);
        if (m->j >= m->i) m->j++;
        m->val = 0;
        return 1;
    }
    m->kind = 0;
    m->t = rndint(d);
    m->i = rndint(K);
    m->j = 0;
    m->val = rndint(GN);
    return m->val != GEL[m->t][m->i];
}

static void do_move(Move *m) {
    if (m->kind == 0) {
        int old = GEL[m->t][m->i];
        set_dart(m->t, m->i, m->val);
        m->val = old;
    } else {
        int tmp = PERM[m->t][m->i];
        PERM[m->t][m->i] = PERM[m->t][m->j];
        PERM[m->t][m->j] = tmp;
        refresh_iperm(m->t);
    }
}

static void random_move(void) {
    for (int tries = 0; tries < 100; tries++) {
        Move mv;
        if (!propose(&mv)) continue;
        do_move(&mv);
        if (simple_ok()) return;
        do_move(&mv);
    }
}

/* Iterated annealing: round 1 starts random. Later rounds start from the incumbent
 * (lowest cost so far) with two random valid moves, at a lower starting temperature.
 * Returns 1 when cost 0 is reached with the current state valid, 0 on timeout. */
static int search_cand(double until) {
    static int bP[MAXD][MAXK], bG[MAXD][MAXK];
    int have = 0;
    long bestc = 0;
    const int iters = 4000;
    while (now() < until) {
        if (!have) {
            random_state();
        } else {
            memcpy(PERM, bP, sizeof PERM);
            memcpy(GEL, bG, sizeof GEL);
            rebuild_all();
            for (int m = 0; m < 2; m++) random_move();
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.03 : 0.08) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            Move mv;
            if (!propose(&mv)) continue;
            do_move(&mv);
            if (!simple_ok()) { do_move(&mv); continue; }
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                do_move(&mv);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(bP, PERM, sizeof PERM);
            memcpy(bG, GEL, sizeof GEL);
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * K * N, K * d * N);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++)
            for (int x = 0; x < N; x++)
                printf("%d %d\n", i * N + x, K * N + PERM[t][i] * N + GFW[t][i][x]);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return x->K - y->K;
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int vlo = atoi(argv[5]), vhi = atoi(argv[6]), kmax = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || kmax < 1) { printf("0 0\n"); return 0; }
    if (kmax > MAXK) kmax = MAXK;

    int nc = 0;
    for (int kk = 1; kk <= kmax; kk++)
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                int N = q * c;
                if (N > MAXN || N < 2 * d) continue;
                int V = 2 * kk * N;
                if (V < vlo || V > vhi) continue;
                if (nc < MAXCAND) cand[nc++] = (Cand){kk, q, p, k, c, N, V};
            }
        }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    static int outP[MAXD][MAXK], outG[MAXD][MAXK];
    int bestV = 0, bestIdx = -1;
    for (int ci = 0; ci < nc; ci++) {
        if (cand[ci].V <= bestV) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.25 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        K = cand[ci].K;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        if (search_cand(now() + slice)) {
            bestV = cand[ci].V;
            bestIdx = ci;
            memcpy(outP, PERM, sizeof PERM);
            memcpy(outG, GEL, sizeof GEL);
        }
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    K = cand[bestIdx].K;
    setup_group(cand[bestIdx].q, cand[bestIdx].p, cand[bestIdx].k, cand[bestIdx].c);
    memcpy(PERM, outP, sizeof PERM);
    memcpy(GEL, outG, sizeof GEL);
    rebuild_all();
    if (cover_cost() != 0 || !simple_ok()) {
        printf("0 0\n");
        return 0;
    }
    print_result();
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Search: multi-orbit affine voltage lifts, ascending in order above the current best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        vlo = max(best[0] + 1, mb // 4)
        vhi = min(mb // 2, 12000)
        if budget > 2.0 and vlo <= vhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi, 3],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

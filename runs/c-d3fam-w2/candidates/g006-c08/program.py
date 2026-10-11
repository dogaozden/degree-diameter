"""Difference-covering search for D = 3 (bi-Cayley / Haar graphs over groups).

For a finite group G of order m and a d-subset S of G, the bipartite graph with parts
a_x, b_x (x in G) and edges a_x ~ b_{xs} (s in S) is d-regular and bipartite on 2m vertices.
It has diameter <= 3 whenever S S^{-1} = G and S^{-1} S = G:
  * a_x reaches a_{x h} for h in S S^{-1}, so same-side pairs are at distance 2;
  * b_y reaches b_{y h} for h in S^{-1} S, so the other same-side pairs are at distance 2;
  * a_x reaches b_{x h} for h in S ∪ S S^{-1} S, which covers G, so cross pairs are at distance <= 3.
The C engine anneals S to make both covers complete, for groups Z_A x| Z_K of order m, and
searches m upward from just above the best Python construction. Python checks every result with
lib.is_valid and keeps the best valid graph (Araujo-Pardo-Lopez, projective plane, or K_{d,d}).
"""
import itertools
import random
import time

import lib

GQ_Q_MAX = 7      # largest q for which W(q) is built in Python (D >= 4 only)
TIME_FRAC = 0.88  # fraction of time_limit given to the C engine
MAX_D_C = 22      # largest d for which the C covering search is used

C_SOURCE = r'''
/* Difference-covering search for bipartite diameter-3 graphs (Haar graphs over groups).
 *
 * Usage:   prog d D seed time_limit [lo]     (stdin is ignored)
 * stdout:  "n m" then m lines "u v": the valid graph of largest order found with
 *          m_group >= lo, or "0 0" if none was found.
 *
 * Group: Z_A x|_R Z_K of order N = A*K, element (a,b) coded as a*K + b.
 * Set S of d distinct elements. Cost = number of elements of G missing from S S^{-1}
 * plus number missing from S^{-1} S. Cost 0 gives a d-regular bipartite graph of
 * diameter <= 3 on 2N vertices. Simulated annealing on S, for m = lo, lo+1, ...
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXG 512
#define MAXV 1024
#define WMAX (MAXV / 64)
#define MAXOPT 8192

static int d, D;
static double t_end;
static double attempt_deadline;

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

/* ------------------------------------------------------------ group tables */

static int GN, GA, GK, GR;
static int rp[MAXG];
static int MUL[MAXG][MAXG];
static int INV[MAXG];

static void set_group(int A, int K, int R) {
    GA = A; GK = K; GR = R; GN = A * K;
    rp[0] = 1 % A;
    for (int b = 1; b < K; b++) rp[b] = (int)((long)rp[b - 1] * R % A);
    for (int x = 0; x < GN; x++) {
        int a1 = x / K, b1 = x % K;
        for (int y = 0; y < GN; y++) {
            int a2 = y / K, b2 = y % K;
            int na = (int)((a1 + (long)rp[b1] * a2) % A);
            int nb = (b1 + b2) % K;
            MUL[x][y] = na * K + nb;
        }
    }
    for (int x = 0; x < GN; x++) {
        int a1 = x / K, b1 = x % K;
        int nb = (K - b1) % K;
        int na = (int)((A - ((long)rp[nb] * a1) % A) % A);
        INV[x] = na * K + nb;
    }
}

/* ------------------------------------------------------------ group options */

typedef struct { int A, K, R; } Opt;
static Opt opts[MAXOPT];
static int nopt;

/* All groups Z_A x|_R Z_K with A*K = m, gcd(R, A) = 1, R^K = 1 mod A. */
static void enum_opts(int m) {
    nopt = 0;
    for (int A = 1; A <= m; A++) {
        if (m % A) continue;
        int K = m / A;
        if (A == 1) {
            if (nopt < MAXOPT) { opts[nopt].A = 1; opts[nopt].K = K; opts[nopt].R = 0; nopt++; }
            continue;
        }
        for (int R = 1; R < A; R++) {
            if (gcd(R, A) != 1) continue;
            if (powmod(R, K, A) != 1 % A) continue;
            if (nopt < MAXOPT) { opts[nopt].A = A; opts[nopt].K = K; opts[nopt].R = R; nopt++; }
        }
    }
}

/* ------------------------------------------------------------ covering search */

static int S[MAXD];
static int best_S[MAXD];
static Opt best_opt;
static int have_best = 0;
static int cnt1[MAXG], cnt2[MAXG];

/* Number of group elements missing from S S^{-1} plus missing from S^{-1} S. */
static int cover_cost(void) {
    int N = GN;
    memset(cnt1, 0, sizeof(int) * N);
    memset(cnt2, 0, sizeof(int) * N);
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            cnt1[MUL[S[i]][INV[S[j]]]]++;
            cnt2[MUL[INV[S[i]]][S[j]]]++;
        }
    int c = 0;
    for (int x = 0; x < N; x++) {
        if (!cnt1[x]) c++;
        if (!cnt2[x]) c++;
    }
    return c;
}

/* Anneal S on the current group. Returns 1 with S covering, or 0 on iteration/time limit. */
static int try_anneal(long iters) {
    int N = GN;
    if (N < d) return 0;
    for (int i = 0; i < d; i++) {
        for (;;) {
            int x = rndint(N), ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == x) { ok = 0; break; }
            if (ok) { S[i] = x; break; }
        }
    }
    int cur = cover_cost();
    if (cur == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 1023) == 0 && now() > attempt_deadline) return 0;
        double T = 0.9 * exp(-6.0 * (double)it / (double)iters) + 0.05;
        int i = rndint(d), x = rndint(N), clash = 0;
        for (int j = 0; j < d; j++) if (S[j] == x) { clash = 1; break; }
        if (clash) continue;
        int old = S[i];
        S[i] = x;
        int nc = cover_cost();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            S[i] = old;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ validity and output */

static uint64_t BUF_A[MAXV][WMAX], BUF_B[MAXV][WMAX];

/* Diameter <= 3 check by bitset balls of radius 3. */
static int valid_d3(int n, int deg[], int adj[][MAXD]) {
    int W = (n + 63) / 64;
    uint64_t (*cur)[WMAX] = BUF_A, (*nxt)[WMAX] = BUF_B;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < 3; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur; cur = nxt; nxt = t;
    }
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(cur[v][w]);
        if (c != n) return 0;
    }
    return 1;
}

static void print_best(void) {
    if (!have_best) { printf("0 0\n"); return; }
    set_group(best_opt.A, best_opt.K, best_opt.R);
    int N = GN, n = 2 * N;
    static int adj[MAXV][MAXD];
    static int deg[MAXV];
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            int y = N + MUL[x][best_S[i]];
            if (deg[x] >= MAXD || deg[y] >= MAXD) { printf("0 0\n"); return; }
            adj[x][deg[x]++] = y;
            adj[y][deg[y]++] = x;
        }
    for (int v = 0; v < n; v++) if (deg[v] > d) { printf("0 0\n"); return; }
    if (!valid_d3(n, deg, adj)) { printf("0 0\n"); return; }
    printf("%d %d\n", n, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + MUL[x][best_S[i]]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lo]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 2;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 3 || d > MAXD) { printf("0 0\n"); return 0; }
    int hi = d * d - d + 1;              /* Moore bound on the group order for D = 3 */
    if (hi > MAXG) hi = MAXG;
    if (lo < d) lo = d;

    int fails = 0;
    for (int m = lo; m <= hi && now() < t_end; m++) {
        enum_opts(m);
        if (nopt == 0) continue;
        double left = t_end - now();
        double tm = left * 0.3;
        if (tm > 6.0) tm = 6.0;
        if (tm < 1.0) tm = 1.0;
        double tm_end = now() + tm;
        int found = 0;
        while (!found && now() < tm_end) {
            Opt o = opts[rndint(nopt)];
            set_group(o.A, o.K, o.R);
            attempt_deadline = tm_end;
            if (try_anneal(30000)) {
                found = 1;
                have_best = 1;
                best_opt = o;
                memcpy(best_S, S, sizeof(int) * d);
            }
        }
        if (found) fails = 0;
        else if (++fails >= 3) break;
    }
    print_best();
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best known construction Python builds directly for (d, D), or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)       # Moore graph, optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                return lib.araujo_lopez_graph(d - 2)           # record 2(q^2+q+5), q = d-2
            except ValueError:
                return None
        return None
    if D >= 4:
        return _best_gq(d)
    return None


def _two_colour(n, edges):
    """Proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
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


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps bipartite)."""
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


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices whose neighbourhoods cover all radius-(D-1) balls (keeps diameter D)."""
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


def _finish(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]           # K_{d,d}: always valid

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    if start is not None:
        cands.append(start)
    elif d >= 3 and D == 3:
        try:
            base = _pg_base(d)
            if base is not None:
                cands.append(base)
                aug = _augment(base[0], base[1], d, seed)
                cands.append(_extend(aug[0], aug[1], d, D, rng,
                                     time.monotonic() + 0.05 * time_limit))
        except Exception:
            pass

    best = _finish(cands, d, D)

    # Moore-extremal start: nothing to search for.
    if start is not None and start[0] >= lib.moore_bound(d, D):
        return best

    if D == 3 and 3 <= d <= MAX_D_C:
        budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 1.5
        if budget > 1.0:
            lo = best[0] // 2 + 1                   # need group order m with 2m > current order
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo],
                                 stdin_graph=None, timeout=budget + 5)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
            except (RuntimeError, ValueError):
                pass                                # keep the valid Python fallback
    return best

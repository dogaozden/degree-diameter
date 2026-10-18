"""Iterated local search over bi-Cayley lifts, with a wider group family (C engine).

Changes from the parent (a deliberately different search, not a tuned SA):
- Group family: metacyclic Z_m x| Z_k (as before) plus direct products Z_m x Z_k.
- Search: iterated local search. Each step samples CAND candidate moves focused on
  unreached (bad) blocks, evaluates each exactly, and takes the best one. It accepts
  sideways moves and occasional uphill moves, and perturbs after stagnation.
- Ratchet: the C engine keeps raising the target order inside one run, seeded by the
  Python best (Araujo-Lopez/projective/GQ baselines, or K_{d,d}).

Safety: every returned graph passes lib.is_valid. Algebraic baselines and K_{d,d} are
kept as fallbacks, and any C failure leaves the best valid graph found so far.
"""
import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXGK 36
#define PENALTY 1000
#define CAND 8

typedef uint64_t u64;

typedef struct { int kind, l, i, j, old, val; } Move;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ---------------- groups: type 0 = Z_m x|_r Z_k, type 1 = Z_m x Z_k ---------------- */
static int gtype, gm, gk, G;
static long long gr;
static int gpw[MAXGK];

static void set_group(int type, int m, int k2, long long r) {
    gtype = type; gm = m; gk = k2; G = m * k2; gr = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { gpw[b] = (int)p; p = (p * r) % m; }
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    if (gtype == 0) {
        long long t = (a + (long long)gpw[b] * c) % gm;
        return (int)(t * gk + (b + e) % gk);
    }
    return ((a + c) % gm) * gk + (b + e) % gk;
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    if (gtype == 0) {
        long long t = ((long long)gpw[nb] * a) % gm;
        long long na = (gm - t) % gm;
        return (int)(na * gk + nb);
    }
    return ((gm - a) % gm) * gk + nb;
}

/* ---------------- lift state ---------------- */
static int DEG, DIA, K, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr = NULL;          /* nbr[l*N + v] */
static u64 *ra = NULL, *rb = NULL;
static u64 FULL;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int sinv = ginv(s);
    int *nl = nbr + (size_t)l * N;
    int q = K + p;
    for (int g = 0; g < G; g++) {
        nl[i * G + g] = q * G + gmul(g, s);
        nl[q * G + g] = i * G + gmul(g, sinv);
    }
}

static int dup_count(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    return dup;
}

/* Cost = unreached (vertex, representative) pairs + penalty per duplicate edge.
   Left translations are automorphisms, so representatives suffice.
   Leaves ra[] valid for the current state. */
static long long evaluate(void) {
    for (int v = 0; v < N; v++) ra[v] = 0;
    for (int b = 0; b < 2 * K; b++) ra[(size_t)b * G] |= (u64)1 << b;
    for (int round = 0; round < DIA; round++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 u = ra[v];
            for (int l = 0; l < DEG; l++) u |= ra[nbr[(size_t)l * N + v]];
            rb[v] = u;
            changed |= (u != ra[v]);
        }
        u64 *t = ra; ra = rb; rb = t;
        if (!changed) break;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += pc64(FULL & ~ra[v]);
    return unr + (long long)PENALTY * dup_count();
}

static void record_solution(void) {
    int m = K * G * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int idx = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < DEG; l++) {
            e[2 * idx] = u;
            e[2 * idx + 1] = nbr[(size_t)l * N + u];
            idx++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = N;
}

/* ---------------- moves ---------------- */
static void do_swap(int l, int i1, int i2) {
    int t = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = t;
    set_dart(l, i1); set_dart(l, i2);
}

static void apply_move(const Move *mv) {
    if (mv->kind == 0) do_swap(mv->l, mv->i, mv->j);
    else { S[mv->l][mv->i] = mv->val; set_dart(mv->l, mv->i); }
}

static void undo_move(const Move *mv) {
    if (mv->kind == 0) do_swap(mv->l, mv->i, mv->j);
    else { S[mv->l][mv->i] = mv->old; set_dart(mv->l, mv->i); }
}

/* Focused move: with prob 1/2 aim at an unreached block, else pick uniformly. */
static void gen_move(Move *mv) {
    int bad_v = -1;
    if (rndu() < 0.5) {
        for (int t = 0; t < 40; t++) {
            int v = rndint(N);
            if ((ra[v] & FULL) != FULL) { bad_v = v; break; }
        }
    }
    if (K >= 2 && rndu() < 0.2) {
        int l = rndint(DEG);
        int i1 = rndint(K), i2 = rndint(K - 1);
        if (i2 >= i1) i2++;
        mv->kind = 0; mv->l = l; mv->i = i1; mv->j = i2; mv->old = 0; mv->val = 0;
        return;
    }
    int l, i;
    if (bad_v >= 0) {
        int block = bad_v / G;
        l = rndint(DEG);
        if (block < K) i = block;
        else {
            i = rndint(K);
            for (int j = 0; j < K; j++)
                if (layers[l][j] == block - K) { i = j; break; }
        }
    } else {
        l = rndint(DEG);
        i = rndint(K);
    }
    mv->kind = 1; mv->l = l; mv->i = i; mv->j = 0;
    mv->old = S[l][i];
    mv->val = rndint(G);
}

/* Iterated local search: best-of-CAND steepest step, sideways moves,
   rare uphill moves, and random perturbation after stagnation. */
static long long ils(long long max_steps, long long patience, int max_restarts, double deadline) {
    long long cur = evaluate();
    long long bestc = cur, last = 0;
    int restarts = 0;
    for (long long t = 0; t < max_steps && cur != 0; t++) {
        if ((t & 7) == 0 && now() > deadline) break;
        if (t - last > patience) {
            if (++restarts > max_restarts) break;
            for (int p = 0; p < 3; p++) {
                Move pm;
                gen_move(&pm);
                apply_move(&pm);
            }
            cur = evaluate();
            bestc = cur;
            last = t;
            continue;
        }
        Move mv[CAND];
        for (int c = 0; c < CAND; c++) gen_move(&mv[c]);
        long long bc = 0;
        int bi = -1;
        for (int c = 0; c < CAND; c++) {
            apply_move(&mv[c]);
            long long c2 = evaluate();
            undo_move(&mv[c]);
            if (bi < 0 || c2 < bc) { bc = c2; bi = c; }
        }
        if (bc <= cur || rndu() < 0.02) {
            apply_move(&mv[bi]);
            if (bc < bestc) { bestc = bc; last = t; }
        }
        cur = evaluate();
    }
    return cur;
}

/* ---------------- group sampling ---------------- */
static const int K2LIST[19] = {1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, int *type, int *pm, int *pk, long long *pr) {
    for (int tries = 0; tries < 300; tries++) {
        int k2 = K2LIST[rndint(19)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (rndu() < 0.5) {
            *type = 1; *pm = m; *pk = k2; *pr = 1;
            return 1;
        }
        long long r = -1;
        if (k2 == 1) r = 1;
        else if (m == 2) r = 1;
        else {
            for (int t = 0; t < 80; t++) {
                long long c = 2 + rndint(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        *type = 0; *pm = m; *pk = k2; *pr = r;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    DIA = D;
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)seed * 2654435761ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    best_n = n0;
    best_m = 0;
    best_e = NULL;
    double deadline = now() + tl;
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < deadline) {
        int k;
        if (rndu() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double s = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rndu();
                if (s > bs) { bs = s; k = kk; }
            }
        }
        int base = best_n / (2 * k);
        int target = base + 1 + rndint(base / 8 + 2);
        if (target < 2) target = 2;

        int type, m, k2;
        long long r;
        if (!sample_group(target, &type, &m, &k2, &r)) continue;
        set_group(type, m, k2, r);
        K = k;
        N = 2 * K * G;
        if (N <= best_n) continue;

        FULL = (((u64)1) << (2 * K)) - 1;
        nbr = malloc(sizeof(int) * (size_t)DEG * N);
        ra = malloc(sizeof(u64) * (size_t)N);
        rb = malloc(sizeof(u64) * (size_t)N);
        if (!nbr || !ra || !rb) {
            free(nbr); free(ra); free(rb);
            nbr = NULL; ra = NULL; rb = NULL;
            break;
        }

        for (int l = 0; l < DEG; l++) {
            for (int i = 0; i < K; i++) layers[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = tmp;
            }
        }
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) set_dart(l, i);

        trials[K]++;
        long long c = ils(3000, 300, 3, deadline);
        if (c == 0) {
            wins[K]++;
            record_solution();
        }
        free(nbr); free(ra); free(rb);
        nbr = NULL; ra = NULL; rb = NULL;
    }

    if (best_m == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", best_n, best_m);
        for (int j = 0; j < best_m; j++)
            printf("%d %d\n", best_e[2 * j], best_e[2 * j + 1]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Algebraic baselines (unchanged from the parent).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add vertices using spare degree; every kept graph is valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main engine: C iterated local search over bi-Cayley lifts, seeded with best_n.
    if d >= 2 and time.monotonic() < deadline - 3.0:
        remaining = deadline - time.monotonic()
        c_budget = max(1.0, 0.9 * remaining)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best_n],
                            stdin_graph=None, timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

"""Bi-Cayley search for d-regular bipartite graphs of diameter D.

Construction: for a finite group G of order n and a set S of d elements, the bipartite graph with
parts A = {a_g} and B = {b_g}, edges a_g ~ b_{g*s} for s in S, is d-regular with 2n vertices.
Left multiplication by G is an automorphism, so the diameter is at most D iff BFS from a_e and from
b_e reaches every vertex within D.

New in this version:
  * Greedy partial-reach seeding: S is grown one generator at a time, each new generator chosen to
    minimise the number of vertices unreached within D by the partial graph (ties broken at random).
    Every second restart uses this seed, the others use random seeds, and simulated annealing refines both.
  * Incumbent-beating schedule: candidate groups are tried in increasing order. A group is attempted
    only if it is larger than the best valid group found so far, so time is spent on groups that can
    improve the result. Metacyclic groups of order above the incumbent fill the remaining time.

The C engine searches S over PSL(2,q), PGL(2,q) and random metacyclic groups. The earlier algebraic
starts and K_{d,d} remain the fallback, and the Python side accepts the C output only if lib.is_valid
confirms it.
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

#define MAXG 2600
#define MAXD 8
#define CODEMAX 90000
#define GM_PGL 0
#define GM_PSL 1
#define GM_SEMI 2
#define MAXORDER 2448

typedef struct { int kind, q, m, k, r, n; } GroupSpec;

static int d, D;
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

static long pw(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ---------- current group (multiplication table) ---------- */
static int kind_cur, qq, SEMI_m, SEMI_k, SEMI_r;
static int rp[MAXG];
static int invt[64];
static int gn, ID;
static int code_of[MAXG];
static int idx_of[CODEMAX];
static int INV[MAXG];
static uint16_t MT[MAXG * MAXG];
static int S[MAXD];

static void dec(int code, int *v) {
    v[3] = code % qq; code /= qq;
    v[2] = code % qq; code /= qq;
    v[1] = code % qq; code /= qq;
    v[0] = code;
}

static int enc4(const int *v) { return ((v[0] * qq + v[1]) * qq + v[2]) * qq + v[3]; }

/* Canonical code of a matrix class: PGL normalises the first nonzero entry to 1; PSL takes min(M, -M). */
static int canon(const int *v) {
    int w[4];
    if (kind_cur == GM_PGL) {
        int f = 1;
        for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
        int inv = invt[f];
        for (int i = 0; i < 4; i++) w[i] = v[i] * inv % qq;
        return enc4(w);
    }
    int neg[4];
    for (int i = 0; i < 4; i++) neg[i] = (qq - v[i]) % qq;
    int a = enc4(v), b = enc4(neg);
    return a < b ? a : b;
}

static int mul_code(int x, int y) {
    if (kind_cur == GM_SEMI) {
        int a = x / SEMI_k, b = x % SEMI_k, c = y / SEMI_k, e = y % SEMI_k;
        int na = (int)(((long)a + (long)rp[b] * c) % SEMI_m);
        return na * SEMI_k + (b + e) % SEMI_k;
    }
    int A[4], B[4], P[4];
    dec(x, A);
    dec(y, B);
    P[0] = (A[0] * B[0] + A[1] * B[2]) % qq;
    P[1] = (A[0] * B[1] + A[1] * B[3]) % qq;
    P[2] = (A[2] * B[0] + A[3] * B[2]) % qq;
    P[3] = (A[2] * B[1] + A[3] * B[3]) % qq;
    return canon(P);
}

static int build_group(const GroupSpec *gs) {
    kind_cur = gs->kind;
    for (int c = 0; c < CODEMAX; c++) idx_of[c] = -1;
    gn = 0;
    if (kind_cur == GM_SEMI) {
        SEMI_m = gs->m; SEMI_k = gs->k; SEMI_r = gs->r;
        if (SEMI_m < 1 || SEMI_k < 1 || SEMI_m * SEMI_k != gs->n || gs->n > MAXG) return 0;
        rp[0] = 1 % SEMI_m;
        for (int b = 1; b < SEMI_k; b++) rp[b] = (int)((long)rp[b - 1] * SEMI_r % SEMI_m);
        gn = gs->n;
        for (int c = 0; c < gn; c++) { code_of[c] = c; idx_of[c] = c; }
        ID = 0;
    } else {
        qq = gs->q;
        if (qq < 3 || qq > 17) return 0;
        for (int x = 1; x < qq; x++) invt[x] = (int)pw(x, qq - 2, qq);
        int total = qq * qq * qq * qq;
        for (int code = 0; code < total; code++) {
            int v[4];
            dec(code, v);
            int det = ((v[0] * v[3] - v[1] * v[2]) % qq + qq) % qq;
            if (kind_cur == GM_PGL ? det == 0 : det != 1) continue;
            if (canon(v) != code) continue;
            if (gn >= MAXG) return 0;
            code_of[gn] = code;
            idx_of[code] = gn;
            gn++;
        }
        if (gn != gs->n) return 0;
        int I[4] = {1, 0, 0, 1};
        ID = idx_of[canon(I)];
    }
    for (int i = 0; i < gn; i++)
        for (int j = 0; j < gn; j++)
            MT[(size_t)i * gn + j] = (uint16_t)idx_of[mul_code(code_of[i], code_of[j])];
    for (int i = 0; i < gn; i++)
        for (int j = 0; j < gn; j++)
            if (MT[(size_t)i * gn + j] == ID) { INV[i] = j; break; }
    return 1;
}

/* ---------- search ---------- */
static int bd[2 * MAXG], bq[2 * MAXG];

/* Number of vertices NOT within distance D of src, using only the first cnt generators of S.
   src < gn: A-side vertex; src >= gn: B-side vertex. */
static int reach_cnt(int src, int cnt) {
    int V = 2 * gn;
    for (int v = 0; v < V; v++) bd[v] = -1;
    int head = 0, tail = 0;
    bd[src] = 0;
    bq[tail++] = src;
    while (head < tail) {
        int v = bq[head++];
        int dv = bd[v];
        if (dv >= D) continue;
        if (v < gn) {
            const uint16_t *row = MT + (size_t)v * gn;
            for (int i = 0; i < cnt; i++) {
                int u = gn + row[S[i]];
                if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
            }
        } else {
            const uint16_t *row = MT + (size_t)(v - gn) * gn;
            for (int i = 0; i < cnt; i++) {
                int u = row[INV[S[i]]];
                if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
            }
        }
    }
    return V - tail;
}

/* Unreached count from both identity vertices (a_e and b_e) using the first cnt generators. */
static int evaluate_cnt(int cnt) { return reach_cnt(ID, cnt) + reach_cnt(gn + ID, cnt); }
static int evaluate(void) { return evaluate_cnt(d); }

static int in_first(int g, int cnt) {
    for (int i = 0; i < cnt; i++) if (S[i] == g) return 1;
    return 0;
}

/* Greedy partial-reach seeding: grow S one generator at a time, minimising the unreached count
   of the partial graph. Ties are broken uniformly at random. Requires gn > d. */
static void greedy_seed(void) {
    int N = gn;
    for (int i = 0; i < d; i++) {
        int bestg = -1, bestf = 0x7fffffff, ties = 0;
        for (int g = 0; g < N; g++) {
            if (in_first(g, i)) continue;
            S[i] = g;
            int f = evaluate_cnt(i + 1);
            if (f < bestf) { bestf = f; bestg = g; ties = 1; }
            else if (f == bestf) {
                ties++;
                if (rndint(ties) == 0) bestg = g;
            }
        }
        S[i] = bestg;
    }
}

static int search_group(double until, int *out) {
    int N = gn;
    if (N <= d) return 0;
    int rounds = 0;
    while (now() < until) {
        if ((rounds & 1) == 0) {
            greedy_seed();
        } else {
            for (int i = 0; i < d; i++) {
                int g;
                do g = rndint(N); while (in_first(g, i));
                S[i] = g;
            }
        }
        rounds++;
        int f = evaluate();
        if (f == 0) { memcpy(out, S, sizeof(int) * d); return 1; }
        const int R = 30000;
        const double T0 = 4.0, T1 = 0.3;
        for (int it = 0; it < R; it++) {
            if ((it & 511) == 0 && now() > until) return 0;
            int i = rndint(d), old = S[i], g;
            do g = rndint(N); while (in_first(g, d));
            S[i] = g;
            int nf = evaluate();
            double T = T0 * pow(T1 / T0, (double)it / R);
            if (nf <= f || rnd01() < exp((double)(f - nf) / T)) f = nf;
            else S[i] = old;
            if (f == 0) { memcpy(out, S, sizeof(int) * d); return 1; }
        }
    }
    return 0;
}

/* Full independent check of the current S: every vertex must reach all others within D. */
static int full_check(void) {
    static int adj[2 * MAXG][MAXD];
    static int dist[2 * MAXG], qu[2 * MAXG];
    int N = gn, V = 2 * N;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) adj[g][i] = N + MT[(size_t)g * N + S[i]];
    for (int h = 0; h < N; h++)
        for (int i = 0; i < d; i++) adj[N + h][i] = MT[(size_t)h * N + INV[S[i]]];
    for (int src = 0; src < V; src++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int v = qu[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static int best_n = 0;     /* vertex count of the incumbent (2 * group order) */
static int best_gn = 0;    /* group order of the incumbent */
static GroupSpec best_spec;
static int bestS[MAXD];

static int try_group(const GroupSpec *gs, double until) {
    if (!build_group(gs)) return 0;
    int out[MAXD];
    if (!search_group(until, out)) return 0;
    memcpy(S, out, sizeof(int) * d);
    if (!full_check()) return 0;
    best_n = 2 * gn;
    best_gn = gn;
    best_spec = *gs;
    memcpy(bestS, out, sizeof(int) * d);
    return 1;
}

/* Random metacyclic group Z_m x| Z_k with order in [lo, hi]. */
static int pick_semi(GroupSpec *gs, int lo, int hi) {
    for (int tries = 0; tries < 200000; tries++) {
        int k = 2 + rndint(40);
        int mlo = (lo + k - 1) / k, mhi = hi / k;
        if (mhi < mlo || mhi < 3) continue;
        int m = mlo + rndint(mhi - mlo + 1);
        if (m < 3) continue;
        int r = 2 + rndint(m - 2);
        if (gcd_i(r, m) != 1) continue;
        if (pw(r, k, m) != 1) continue;
        gs->kind = GM_SEMI; gs->q = 0; gs->m = m; gs->k = k; gs->r = r; gs->n = m * k;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.93;
    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    /* Ascending order: each candidate is attempted only if it beats the incumbent group order. */
    static const struct { int kind, q; double frac; } plan[] = {
        {GM_PSL, 11, 0.04}, {GM_PSL, 13, 0.18}, {GM_PGL, 11, 0.30},
        {GM_PGL, 13, 0.30}, {GM_PSL, 17, 0.30}};
    for (size_t s = 0; s < (sizeof(plan) / sizeof(plan[0])); s++) {
        double tn = now();
        if (tn >= t_end) break;
        GroupSpec gs;
        memset(&gs, 0, sizeof gs);
        gs.kind = plan[s].kind;
        gs.q = plan[s].q;
        int qv = gs.q;
        gs.n = (gs.kind == GM_PGL) ? qv * (qv * qv - 1) : qv * (qv * qv - 1) / 2;
        if (gs.n <= best_gn) continue;
        double until = tn + plan[s].frac * (t_end - tn);
        if (until > t_end) until = t_end;
        try_group(&gs, until);
    }

    /* Metacyclic groups strictly larger than the incumbent. */
    while (now() < t_end) {
        int lo = best_gn + 1;
        if (lo < 1000) lo = 1000;
        int hi = MAXORDER;
        if (lo > hi) break;
        GroupSpec gs;
        memset(&gs, 0, sizeof gs);
        if (!pick_semi(&gs, lo, hi)) break;
        double until = now() + 2.0;
        if (until > t_end) until = t_end;
        try_group(&gs, until);
    }

    if (best_n == 0 || !build_group(&best_spec)) { printf("0 0\n"); return 0; }
    memcpy(S, bestS, sizeof(int) * d);
    int N = gn;
    long E = (long)N * d;
    printf("%d %ld\n", 2 * N, E);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + MT[(size_t)g * N + S[i]]);
    return 0;
}
'''


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

    # Safe fallback: K_{d,d} or the best algebraic start.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 8 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best

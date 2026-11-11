"""Bi-Cayley search over non-metacyclic groups for the weakest target (d=4, D=7).

Change from the parent: the lift search is replaced by a different construction. A bi-Cayley
graph over a group G of order N has vertices (g,0), (g,1) with (g,0) ~ (g*s,1) for s in S, |S| = d.
The left-regular action of G is by automorphisms, so the diameter is exact from two BFS runs
(from (e,0) and (e,1)). The group sweep ascends through orders N, so each success is a valid
graph, and the largest success is kept. Groups include cyclic, Z_a x Z_b, Z_m x| Z_k, and
direct products of PSL(2,5), PGL(2,5), PSL(2,7), PGL(2,7) with Z_k (non-metacyclic).
Every output is re-checked with lib.is_valid, and the start graph is kept as the fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search over sweeping group orders.
 * Usage:  prog d D seed time_limit  < (ignored)
 * stdout: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXS 1100
#define MAXD 16
#define MAXBASE 336
#define NBASE 4
#define MAXE (MAXS * MAXD)

static int d, D;
static int NT;             /* target group order for the current attempt */
static int N;              /* group order actually built */
static int GT[MAXS * MAXS];
static int INV[MAXS];
static int S[MAXD];
static int dist[2 * MAXS];
static int Q[2 * MAXS];

static int best_n = 0, best_m = 0;
static int best_e[2 * MAXE];
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
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

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------- base groups */
typedef struct { unsigned char p[8]; } Perm;
static Perm EL[MAXBASE];
static int base_n[NBASE];
static int *base_tab[NBASE];

static int find_perm(const Perm *h, int cnt, int s) {
    for (int i = 0; i < cnt; i++)
        if (memcmp(EL[i].p, h->p, (size_t)s) == 0) return i;
    return -1;
}

/* PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) acting on p+1 points; table stored in base_tab[slot]. */
static int build_base(int p, int pgl, int slot) {
    int s = p + 1, inf = p, prim = 1, ng = 0, cnt = 0;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x < s; x++)
        gen[ng].p[x] = (unsigned char)(x == inf ? inf : (x + 1) % p);
    ng++;
    for (int x = 0; x < s; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[ng].p[x] = (unsigned char)v;
    }
    ng++;
    if (pgl) {
        for (int x = 0; x < s; x++)
            gen[ng].p[x] = (unsigned char)(x == inf ? inf : (x * prim) % p);
        ng++;
    }
    memset(&EL[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) EL[0].p[x] = (unsigned char)x;
    cnt = 1;
    for (int qi = 0; qi < cnt; qi++)
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[qi].p[gen[k].p[x]];
            if (find_perm(&h, cnt, s) < 0) {
                if (cnt >= MAXBASE) return 0;
                EL[cnt++] = h;
            }
        }
    int *tab = malloc(sizeof(int) * (size_t)cnt * (size_t)cnt);
    if (!tab) return 0;
    for (int i = 0; i < cnt; i++)
        for (int j = 0; j < cnt; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[i].p[EL[j].p[x]];
            int idx = find_perm(&h, cnt, s);
            if (idx < 0) { free(tab); return 0; }
            tab[i * cnt + j] = idx;
        }
    base_tab[slot] = tab;
    base_n[slot] = cnt;
    return 1;
}

static void init_bases(void) {
    for (int b = 0; b < NBASE; b++) { base_tab[b] = NULL; base_n[b] = 0; }
    build_base(5, 0, 0);
    build_base(5, 1, 1);
    build_base(7, 0, 2);
    build_base(7, 1, 3);
}

/* ---------------------------------------------------------- group tables */
static void finish_group(void) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { INV[x] = y; break; }
}

static void set_cyclic(int n) {
    N = n;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            GT[x * N + y] = (x + y) % N;
    finish_group();
}

static void set_abelian(int a, int b) {
    N = a * b;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int x1 = x / b, x2 = x % b, y1 = y / b, y2 = y % b;
            GT[x * N + y] = ((x1 + y1) % a) * b + (x2 + y2) % b;
        }
    finish_group();
}

/* Z_m x|_r Z_k, element a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_semidirect(int m, int k, int r) {
    N = m * k;
    int rp[MAXS];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    finish_group();
}

/* Non-metacyclic base group times Z_k. */
static void set_base_times(int slot, int k) {
    int o = base_n[slot];
    N = o * k;
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] =
                        base_tab[slot][x * o + y] * k + (c + e) % k;
    finish_group();
}

static int pick_group(void) {
    int type = rndint(4);
    if (type == 1) {
        for (int t = 0; t < 100; t++) {
            int a = 2 + rndint(NT / 2 - 1);
            if (NT % a == 0 && NT / a >= 2) { set_abelian(a, NT / a); return 1; }
        }
    } else if (type == 2) {
        for (int t = 0; t < 100; t++) {
            int m = 2 + rndint(NT / 2 - 1);
            if (NT % m) continue;
            int k = NT / m;
            int r = 2 + rndint(m > 2 ? m - 2 : 1);
            if (m > 2 && gcdi(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                set_semidirect(m, k, r);
                return 1;
            }
        }
    } else if (type == 3) {
        int b = rndint(NBASE);
        if (base_tab[b] && NT % base_n[b] == 0) {
            set_base_times(b, NT / base_n[b]);
            return 1;
        }
    }
    set_cyclic(NT);
    return 1;
}

/* ---------------------------------------------------------- search */
/* Bad count: unreached (source, vertex) pairs over sources (e,0) and (e,1). Zero iff diameter <= D.
 * Valid because the group acts regularly on each side by left multiplication. */
static long eval_bad(void) {
    long bad = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < 2 * N; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s0] = 0;
        Q[t++] = s0;
        while (h < t) {
            int v = Q[h++];
            int dv = dist[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + GT[v * N + S[i]];
                    if (dist[u] < 0) { dist[u] = dv + 1; Q[t++] = u; }
                }
            } else {
                int hh = v - N;
                for (int i = 0; i < d; i++) {
                    int u = GT[hh * N + INV[S[i]]];
                    if (dist[u] < 0) { dist[u] = dv + 1; Q[t++] = u; }
                }
            }
        }
        bad += 2L * N - t;
    }
    return bad;
}

static int in_S(int t, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == t) return 1;
    return 0;
}

static int climb(int steps) {
    for (int i = 0; i < d; i++) {
        int t;
        do { t = rndint(N); } while (in_S(t, i));
        S[i] = t;
    }
    long bad = eval_bad();
    double T = 1.0;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        int i = rndint(d);
        int old = S[i];
        int t;
        do { t = rndint(N); } while (in_S(t, d));
        S[i] = t;
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            S[i] = old;
        }
        T *= 0.997;
        if (T < 0.1) T = 0.1;
    }
    return bad == 0;
}

static void record_best(void) {
    int n2 = 2 * N;
    if (n2 <= best_n) return;
    int m = 0;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) {
            best_e[2 * m] = g;
            best_e[2 * m + 1] = N + GT[g * N + S[i]];
            m++;
        }
    best_n = n2;
    best_m = m;
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
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    int ch;
    while ((ch = getchar()) != EOF) {}

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    long nmax = moore / 2;
    if (nmax > MAXS) nmax = MAXS;
    init_bases();

    int start = d + 2 > 16 ? d + 2 : 16;
    for (NT = start; NT <= nmax && now() < t_end; NT++) {
        if (NT < d) continue;
        int attempts = NT >= 400 ? 8 : 3;
        int steps = NT >= 300 ? 3000 : 1000;
        int ok = 0;
        for (int a = 0; a < attempts && !ok && now() < t_end; a++) {
            pick_group();
            if (climb(steps)) ok = 1;
        }
        if (ok) record_best();
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
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
    """Algebraic candidates valid for diameter D (may be empty). Each is checked before use."""
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

    # K_{d,d} is always valid for D >= 2: the safe fallback.
    best = lib.haar_graph(d, range(d))
    try:
        cands = known_starts(d, D)
    except Exception:
        cands = []
    for n, e in cands:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    # Spend most of the case budget in the C engine; keep margin for compile and output.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

"""Bi-Cayley search over explicit groups for the weakest target (d=4, D=7).

Change from the parent: the voltage-lift search is replaced by a bi-Cayley family. A graph on 2N
vertices has A-vertices a_x and B-vertices b_y, with a_x adjacent to b_{x*s} for each of d
connection elements s. Left multiplication by a group element is an automorphism, so the graph's
diameter is at most D exactly when BFS from a_e and from b_e reaches every vertex within D. Each
BFS costs O(N*d), so simulated annealing over the connection set can test very many candidates.
The groups are metacyclic Z_m x|_r Z_k times Z_c, and PSL(2,p)/PGL(2,p) times Z_c.

The C program ignores the start graph and prints the largest valid bi-Cayley graph it finds, or
"0 0". Python keeps the algebraic start (Haar, projective plane, Araujo-Lopez, generalized
quadrangle, or hexagon) unless the C output is strictly larger and passes lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search core.
 * Usage: prog d D seed time_limit [min_hint]   (stdin is ignored)
 * Output: "n m" then m lines "u v" of the largest valid graph found, or "0 0".
 * A group G of order N acts regularly on A = {a_x} and B = {b_y}; edges a_x - b_{x s}, s in S.
 * Cost = sum over the two sources a_e, b_e of (excess distance beyond D) + 2 per unreached vertex.
 * Cost 0 means diameter <= D for the whole graph.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDEG 8
#define MAXG 1100
#define MAXBO 1400
#define MAXDESC 8192
#define NBASE 5
#define SPAN 24
#define STEPS 40000

static int dd, DD;
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

static int gcd(int a, int b) {
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

static long moore_b(int d, int D) {
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

/* ---------------------------------------------------------------- base permutation groups */
typedef struct { unsigned char p[12]; } Perm;
typedef struct { uint64_t k; int i; } KI;
typedef struct { int ord; int *tab; } Base;

static Base BASE[NBASE];
static const int BP[NBASE] = {5, 5, 7, 7, 11};
static const int BPGL[NBASE] = {0, 1, 0, 1, 0};
static Perm EL[MAXBO];
static uint64_t EK[MAXBO];
static KI SKI[MAXBO];

static uint64_t pkey(const Perm *x, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)x->p[i] << (4 * i);
    return k;
}

static int find_key(uint64_t key, int n) {
    for (int i = 0; i < n; i++)
        if (EK[i] == key) return i;
    return -1;
}

static int cmpki(const void *a, const void *b) {
    uint64_t x = ((const KI *)a)->k, y = ((const KI *)b)->k;
    return x < y ? -1 : (x > y);
}

static int lookup_key(uint64_t key, int n) {
    int lo = 0, hi = n - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (SKI[mid].k == key) return SKI[mid].i;
        if (SKI[mid].k < key) lo = mid + 1;
        else hi = mid - 1;
    }
    return -1;
}

/* Action on P^1(F_p) = {0..p-1, inf = p}. Identity is element 0. */
static int build_base(int p, int pgl, Base *B) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1; e++)
            if (powmod(c, e, p) == 1) { ok = 0; break; }
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x < s; x++)
        gen[0].p[x] = (unsigned char)(x == inf ? inf : (x + 1) % p);
    for (int x = 0; x < s; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[1].p[x] = (unsigned char)v;
    }
    ng = 2;
    if (pgl) {
        for (int x = 0; x < s; x++)
            gen[2].p[x] = (unsigned char)(x == inf ? inf : (x * prim) % p);
        ng = 3;
    }
    for (int x = 0; x < s; x++) EL[0].p[x] = (unsigned char)x;
    EK[0] = pkey(&EL[0], s);
    int n = 1;
    for (int qi = 0; qi < n; qi++)
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[qi].p[gen[k].p[x]];
            uint64_t key = pkey(&h, s);
            if (find_key(key, n) < 0) {
                if (n >= MAXBO) return 0;
                EL[n] = h;
                EK[n] = key;
                n++;
            }
        }
    for (int i = 0; i < n; i++) { SKI[i].k = EK[i]; SKI[i].i = i; }
    qsort(SKI, (size_t)n, sizeof(KI), cmpki);
    int *tab = malloc(sizeof(int) * (size_t)n * (size_t)n);
    if (!tab) return 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[i].p[EL[j].p[x]];
            int idx = lookup_key(pkey(&h, s), n);
            tab[(size_t)i * n + j] = idx < 0 ? 0 : idx;
        }
    B->ord = n;
    B->tab = tab;
    return 1;
}

static void init_bases(void) {
    for (int b = 0; b < NBASE; b++) {
        BASE[b].ord = 0;
        BASE[b].tab = NULL;
        if (!build_base(BP[b], BPGL[b], &BASE[b])) BASE[b].ord = 0;
    }
}

/* ---------------------------------------------------------------- groups as mult tables */
static int NG;
static int GT[MAXG * MAXG];
static int INV[MAXG];
static int RP[MAXG];

typedef struct { int kind, m, k, r, c, bi; } Desc;
static Desc DS[MAXDESC];
static int nds;

static void add_desc(Desc x) {
    if (nds < MAXDESC) DS[nds++] = x;
}

static void enum_desc(int N) {
    nds = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int R = N / m;
        for (int k = 1; k <= R; k++) {
            if (R % k) continue;
            int c = R / k;
            int rl = (m == 1) ? 1 : m;
            for (int r = 0; r < rl; r++) {
                if (m > 1 && gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                Desc g;
                memset(&g, 0, sizeof g);
                g.kind = 0; g.m = m; g.k = k; g.r = r; g.c = c;
                add_desc(g);
            }
        }
    }
    for (int b = 0; b < NBASE; b++) {
        if (BASE[b].ord > 0 && N % BASE[b].ord == 0) {
            Desc g;
            memset(&g, 0, sizeof g);
            g.kind = 1; g.bi = b; g.c = N / BASE[b].ord;
            add_desc(g);
        }
    }
}

static void build_group(const Desc *g) {
    int N;
    if (g->kind == 0) {
        int m = g->m, k = g->k, r = g->r, c = g->c;
        N = m * k * c;
        NG = N;
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        for (int x = 0; x < N; x++) {
            int a1 = x / (k * c), b1 = (x / c) % k, e1 = x % c;
            for (int y = 0; y < N; y++) {
                int a2 = y / (k * c), b2 = (y / c) % k, e2 = y % c;
                int a = (int)(((long)a1 + (long)RP[b1] * a2) % m);
                int b = (b1 + b2) % k;
                int e = (e1 + e2) % c;
                GT[x * N + y] = (a * k + b) * c + e;
            }
        }
    } else {
        Base *B = &BASE[g->bi];
        int o = B->ord, c = g->c;
        N = o * c;
        NG = N;
        for (int x = 0; x < N; x++) {
            int bi1 = x / c, e1 = x % c;
            for (int y = 0; y < N; y++) {
                int bi2 = y / c, e2 = y % c;
                GT[x * N + y] = B->tab[bi1 * o + bi2] * c + (e1 + e2) % c;
            }
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------------- bi-Cayley search */
static int S[MAXDEG];
static int dq[2 * MAXG], qq[2 * MAXG];
static int BU[MAXG * MAXDEG], BV[MAXG * MAXDEG];
static int best_n = 0, best_m = 0;

/* Sum of excess distances from a_e and b_e. Zero iff the bi-Cayley graph has diameter <= DD. */
static long eval_cost(void) {
    int N = NG, V = 2 * N;
    long cost = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) dq[v] = -1;
        int h = 0, t = 0;
        dq[s0] = 0;
        qq[t++] = s0;
        while (h < t) {
            int v = qq[h++];
            int dv = dq[v] + 1;
            if (v < N) {
                for (int i = 0; i < dd; i++) {
                    int u = N + GT[v * N + S[i]];
                    if (dq[u] < 0) { dq[u] = dv; qq[t++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < dd; i++) {
                    int u = GT[y * N + INV[S[i]]];
                    if (dq[u] < 0) { dq[u] = dv; qq[t++] = u; }
                }
            }
        }
        for (int v = 0; v < V; v++) {
            if (dq[v] < 0) cost += 2;
            else if (dq[v] > DD) cost += dq[v] - DD;
        }
    }
    return cost;
}

static int inS(int g, int k) {
    for (int i = 0; i < k; i++)
        if (S[i] == g) return 1;
    return 0;
}

static int anneal(int N, double until) {
    for (int i = 0; i < dd; i++) {
        int g;
        do g = rndint(N); while (inS(g, i));
        S[i] = g;
    }
    long cur = eval_cost();
    double T = 1.0;
    for (long st = 0; st < STEPS && cur > 0; st++) {
        if ((st & 63) == 0 && now() > until) return 0;
        int i = rndint(dd), g = rndint(N);
        if (inS(g, dd)) continue;
        int old = S[i];
        S[i] = g;
        long nv = eval_cost();
        if (nv <= cur || rnd01() < exp(-(double)(nv - cur) / T)) cur = nv;
        else S[i] = old;
        T *= 0.9995;
        if (T < 0.3) T = 0.3;
    }
    if (cur != 0) return 0;
    int cnt = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < dd; i++) {
            BU[cnt] = x;
            BV[cnt] = N + GT[x * N + S[i]];
            cnt++;
        }
    best_n = 2 * N;
    best_m = cnt;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [hint]\n", argv[0]);
        return 2;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int hint = argc > 5 ? atoi(argv[5]) : 0;
    if (dd < 2 || dd > MAXDEG || DD < 2) { printf("0 0\n"); return 0; }

    t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long Nhi = moore_b(dd, DD) / 2;
    if (Nhi > MAXG) Nhi = MAXG;
    init_bases();

    int cur = hint - 1;
    if (cur < dd - 1) cur = dd - 1;
    while (now() < t_end && cur + 1 <= Nhi) {
        int N = cur + 1 + rndint(SPAN);
        if (N > Nhi) N = (int)Nhi;
        enum_desc(N);
        if (nds == 0) continue;
        Desc g = DS[rndint(nds)];
        build_group(&g);
        if (anneal(N, t_end)) cur = N;
    }

    if (best_n == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++) printf("%d %d\n", BU[i], BV[i]);
    }
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention yields a graph that passes lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 8 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best

    # Hint: the C search only has to beat best.n, so it needs N = n/2 + 1 or more.
    hint = best[0] // 2 + 1
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), hint],
                         stdin_graph=None, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

"""Combined search: voltage lifts over groups (bi-Cayley when p = 1) with orbit-reduced diameter checks.

Python builds the best algebraic start (PG(2,q), Araujo-Pardo-Lopez, W(q) or K_{d,d}) and checks it with
lib.is_valid. The C engine then searches for a larger valid graph: a random group (PSL(2,q), PGL(2,q) or a
metacyclic group Z_m x| Z_k), a base multigraph on p + p fibres (p = 1..4), and simulated annealing over
the voltages. Only the 2p fibre representatives need BFS, because the group acts regularly on each fibre.
The C output is accepted only after an independent full-graph diameter check and lib.is_valid.
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

#define MAXG 2700
#define MAXD 8
#define MAXP 4
#define MAXND (MAXD * MAXP)
#define MAXV (2 * MAXP * MAXG)
#define MAXE (MAXD * MAXP * MAXG)
#define CODEMAX 90000
#define STEPS 20000

enum { GM_PGL = 0, GM_PSL = 1, GM_SEMI = 2 };

typedef struct { int kind, q, m, k, r; } Spec;

static int d, D;
static double t_end;
static long moore;
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

static long compute_moore(void) {
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

/* ---------------- group tables ---------------- */
static int qq, kind_cur;
static int invt[32];
static int rp[MAXG];
static int gn, ID;
static int code_of[MAXG];
static int idx_of[CODEMAX];
static int INV[MAXG];
static uint16_t MT[MAXG * MAXG];

static void dec(int code, int *v) {
    v[3] = code % qq; code /= qq;
    v[2] = code % qq; code /= qq;
    v[1] = code % qq; code /= qq;
    v[0] = code;
}

static int enc4(const int *v) { return ((v[0] * qq + v[1]) * qq + v[2]) * qq + v[3]; }

static int canon(const int *v) {
    int w[4];
    if (kind_cur == GM_PGL) {
        int f = 1;
        for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
        int iv = invt[f];
        for (int i = 0; i < 4; i++) w[i] = v[i] * iv % qq;
        return enc4(w);
    }
    int ng[4];
    for (int i = 0; i < 4; i++) ng[i] = (qq - v[i]) % qq;
    int a = enc4(v), b = enc4(ng);
    return a < b ? a : b;
}

static int mat_mul_code(int x, int y) {
    int A[4], B[4], P4[4];
    dec(x, A);
    dec(y, B);
    P4[0] = (A[0] * B[0] + A[1] * B[2]) % qq;
    P4[1] = (A[0] * B[1] + A[1] * B[3]) % qq;
    P4[2] = (A[2] * B[0] + A[3] * B[2]) % qq;
    P4[3] = (A[2] * B[1] + A[3] * B[3]) % qq;
    return canon(P4);
}

static int build_group(const Spec *s) {
    gn = 0;
    if (s->kind == GM_SEMI) {
        int m = s->m, k = s->k, n = m * k;
        if (m < 1 || k < 1 || n > MAXG) return 0;
        rp[0] = 1 % m;
        for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * s->r % m);
        gn = n;
        ID = 0;
        for (int x = 0; x < n; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < n; y++) {
                int c = y / k, e = y % k;
                int na = (int)(((long)a + (long)rp[b] * c) % m);
                MT[x * n + y] = (uint16_t)(na * k + (b + e) % k);
            }
        }
    } else {
        qq = s->q;
        if (qq < 3 || qq > 17) return 0;
        kind_cur = s->kind;
        for (int x = 1; x < qq; x++) invt[x] = (int)pw(x, qq - 2, qq);
        for (int c = 0; c < CODEMAX; c++) idx_of[c] = -1;
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
        int I4[4] = {1, 0, 0, 1};
        ID = idx_of[canon(I4)];
        if (ID < 0) return 0;
        for (int i = 0; i < gn; i++)
            for (int j = 0; j < gn; j++)
                MT[i * gn + j] = (uint16_t)idx_of[mat_mul_code(code_of[i], code_of[j])];
    }
    if (gn <= d + 1) return 0;
    for (int i = 0; i < gn; i++) {
        INV[i] = -1;
        for (int j = 0; j < gn; j++)
            if (MT[(size_t)i * gn + j] == ID) { INV[i] = j; break; }
        if (INV[i] < 0) return 0;
    }
    return 1;
}

/* ---------------- lift state ---------------- */
static int P, nd;
static int dI[MAXND], dJ[MAXND], dG[MAXND];
static int oc[MAXP], ol[MAXP][MAXD], ic[MAXP], il[MAXP][MAXD];

/* Random d-regular base: d permutations of p fibres, so every fibre has d darts out and d in. */
static void make_base(int p) {
    P = p;
    nd = d * p;
    for (int i = 0; i < p; i++) { oc[i] = 0; ic[i] = 0; }
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < p; i++) {
            dI[s * p + i] = i;
            dJ[s * p + i] = perm[i];
        }
    }
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t];
        ol[i][oc[i]++] = t;
        il[j][ic[j]++] = t;
    }
}

/* True if some dart u != t with the same base arc as t already carries voltage g. */
static int clash(int t, int g, int limit) {
    for (int u = 0; u < limit; u++)
        if (u != t && dI[u] == dI[t] && dJ[u] == dJ[t] && dG[u] == g) return 1;
    return 0;
}

static void random_voltages(void) {
    for (int t = 0; t < nd; t++) {
        int g;
        do g = rndint(gn); while (clash(t, g, t));
        dG[t] = g;
    }
}

static int stv[MAXV], dep[MAXV], qu[MAXV];
static int stc = 0;

/* Sum over the 2p fibre representatives of vertices NOT within distance D.
 * Zero iff the lift has diameter <= D, because the group acts regularly on every fibre. */
static long orbit_bad(void) {
    int half = P * gn, V = 2 * half;
    long total = 0;
    for (int b = 0; b < 2 * P; b++) {
        if (++stc == 0x7fffffff) { memset(stv, 0, sizeof stv); stc = 1; }
        int src = b * gn + ID;
        int head = 0, tail = 0;
        stv[src] = stc;
        dep[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int v = qu[head++], dv = dep[v];
            if (dv >= D) continue;
            if (v < half) {
                int i = v / gn, x = v - i * gn;
                const uint16_t *row = MT + (size_t)x * gn;
                for (int k = 0; k < oc[i]; k++) {
                    int t = ol[i][k];
                    int u = (P + dJ[t]) * gn + row[dG[t]];
                    if (stv[u] != stc) { stv[u] = stc; dep[u] = dv + 1; qu[tail++] = u; }
                }
            } else {
                int j = (v - half) / gn, y = v - half - j * gn;
                const uint16_t *row = MT + (size_t)y * gn;
                for (int k = 0; k < ic[j]; k++) {
                    int t = il[j][k];
                    int u = dI[t] * gn + row[INV[dG[t]]];
                    if (stv[u] != stc) { stv[u] = stc; dep[u] = dv + 1; qu[tail++] = u; }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static long anneal(int steps, double until) {
    long bad = orbit_bad();
    const double T0 = 2.0, T1 = 0.05;
    for (int it = 0; it < steps && bad > 0; it++) {
        if ((it & 127) == 0 && now() > until) break;
        int t = rndint(nd), old = dG[t], g;
        do g = rndint(gn); while (clash(t, g, nd));
        dG[t] = g;
        long nb = orbit_bad();
        double T = T0 * pow(T1 / T0, (double)it / steps);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dG[t] = old;
    }
    return bad;
}

/* ---------------- best graph ---------------- */
static int best_n = 0, have = 0, best_m = 0;
static int EU[MAXE], EV[MAXE], BU[MAXE], BV[MAXE];
static int adjF[MAXV][MAXD], degF[MAXV];
static int fst[MAXV], fdep[MAXV], fq[MAXV];
static int fstc = 0;

/* Independent full check on the explicit graph: degrees, A-B edges and all-pairs distance <= D. */
static int full_ok(int V, int m, int half) {
    for (int v = 0; v < V; v++) degF[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = EU[e], v = EV[e];
        if (u < 0 || v < 0 || u >= V || v >= V || u == v) return 0;
        if ((u < half) == (v < half)) return 0;
        if (degF[u] >= d || degF[v] >= d) return 0;
        adjF[u][degF[u]++] = v;
        adjF[v][degF[v]++] = u;
    }
    for (int src = 0; src < V; src++) {
        ++fstc;
        int head = 0, tail = 0;
        fst[src] = fstc;
        fdep[src] = 0;
        fq[tail++] = src;
        while (head < tail) {
            int v = fq[head++], dv = fdep[v];
            if (dv >= D) continue;
            for (int k = 0; k < degF[v]; k++) {
                int u = adjF[v][k];
                if (fst[u] != fstc) { fst[u] = fstc; fdep[u] = dv + 1; fq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static int record(void) {
    int half = P * gn, V = 2 * half, m = 0;
    if (V <= best_n) return 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < gn; x++) {
            EU[m] = dI[t] * gn + x;
            EV[m] = (P + dJ[t]) * gn + MT[(size_t)x * gn + dG[t]];
            m++;
        }
    if (m > MAXE || !full_ok(V, m, half)) return 0;
    best_n = V;
    best_m = m;
    have = 1;
    memcpy(BU, EU, sizeof(int) * m);
    memcpy(BV, EV, sizeof(int) * m);
    return 1;
}

/* ---------------- group choice ---------------- */
static const Spec ALG[] = {
    {GM_PSL, 5, 0, 0, 0}, {GM_PSL, 7, 0, 0, 0}, {GM_PSL, 11, 0, 0, 0},
    {GM_PSL, 13, 0, 0, 0}, {GM_PSL, 17, 0, 0, 0},
    {GM_PGL, 5, 0, 0, 0}, {GM_PGL, 7, 0, 0, 0}, {GM_PGL, 11, 0, 0, 0},
    {GM_PGL, 13, 0, 0, 0}};

static int group_order(const Spec *s) {
    if (s->kind == GM_SEMI) return s->m * s->k;
    long q = s->q, o = q * (q * q - 1);
    return (int)(s->kind == GM_PSL ? o / 2 : o);
}

/* Pick a group of order in [lo, hi]: algebraic with prob 0.3, else metacyclic Z_m x| Z_k. */
static int pick_spec(int lo, int hi, Spec *s) {
    if (rndint(10) < 3) {
        int cand[9], nc = 0;
        for (int i = 0; i < 9; i++) {
            int o = group_order(&ALG[i]);
            if (o >= lo && o <= hi) cand[nc++] = i;
        }
        if (nc) { *s = ALG[cand[rndint(nc)]]; return 1; }
    }
    static int divs[MAXG];
    for (int tries = 0; tries < 60; tries++) {
        int N;
        if (rndint(2)) N = lo + rndint(hi - lo + 1);
        else N = (int)exp(log((double)lo) + rnd01() * (log((double)hi + 1.0) - log((double)lo)));
        if (N < lo) N = lo;
        if (N > hi) N = hi;
        int nv = 0;
        for (int k = 2; k <= N / 2; k++) if (N % k == 0) divs[nv++] = k;
        if (!nv) continue;
        int k = divs[rndint(nv)], m = N / k;
        int r = 1;
        for (int t = 0; t < 30; t++) {
            int rr = 1 + rndint(m - 1);
            if (gcd_i(rr, m) == 1 && pw(rr, k, m) == 1 % m) { r = rr; break; }
        }
        s->kind = GM_SEMI;
        s->q = 0;
        s->m = m;
        s->k = k;
        s->r = r;
        return 1;
    }
    return 0;
}

static void search(double until) {
    while (now() < until) {
        int lo = best_n / (2 * MAXP) + 1;
        if (lo < d + 2) lo = d + 2;
        int hi = (int)(moore / 2);
        if (hi > MAXG) hi = MAXG;
        if (lo > hi) return;
        Spec s;
        if (!pick_spec(lo, hi, &s)) return;
        if (!build_group(&s)) continue;
        double ep_end = now() + 1.5 + 2.5 * rnd01();
        if (ep_end > until) ep_end = until;
        while (now() < ep_end) {
            int ps[MAXP], np = 0;
            for (int p = 1; p <= MAXP; p++) {
                long V = 2L * p * gn;
                if (V > best_n && V <= moore) ps[np++] = p;
            }
            if (!np) break;
            int p = ps[rndint(np)];
            make_base(p);
            random_voltages();
            long bad = anneal(STEPS, ep_end);
            if (bad == 0) record();
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int startn = argc > 5 ? atoi(argv[5]) : 0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.92;
    moore = compute_moore();
    best_n = startn;
    if (d < 3 || d > MAXD || D < 2 || moore <= best_n) { printf("0 0\n"); return 0; }
    search(t_end);
    if (!have) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", BU[e], BV[e]);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 3)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best

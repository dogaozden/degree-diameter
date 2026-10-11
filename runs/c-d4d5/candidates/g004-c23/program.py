"""Bold variant: for D >= 4 (and D = 3 when no plane is available), search directly over
multi-orbit voltage lifts of groups Z_m x|_r Z_k with a fast C annealer, instead of
extending the parent's graphs. Bisection runs over the half-order T (n = 2T). Algebraic
optima (PG(2,q) for D=3, W(q) for D=4) are returned immediately when they apply, and
every candidate is checked with lib.is_valid before it is kept."""
import itertools
import math
import random
import time

import lib

S_LIST = (1, 2, 3, 4, 5, 6)     # base orbits per side, s
MAXM = 400                      # largest group order passed to C
TCAP = 2400                     # largest half-order T (n = 2T <= 4800)
PRES_PER_ORDER = 2              # group presentations tried per (T, s)
GQ_Q_MAX = 9                    # largest q for which W(q) is built
LIFT_FRAC = 0.2                 # share of remaining time per bisection step
LIFT_MAX_BUDGET = 6.0           # cap on one bisection step (seconds)
TIME_FRAC = 0.8                 # fraction of time_limit used overall


# ---------------------------------------------------------------- C annealer
#
# Input (stdin, via lib.run_c as a fake graph): flat list [M] + mul table (M*M, row-major,
# mul[x*M+g] = x*g) + inverses (M). Arguments: d D s M seed budget.
# Vertices: left (i,x) -> i*M+x, right (j,y) -> s*M + j*M + y.
# Left (i,x) dart kk -> right (sig[kk][i], x*G[kk][i]); right (j,y) dart kk -> left
# (sinv[kk][j], y*G^-1). Left multiplication by a group element is an automorphism, so
# distances from the 2s orbit representatives decide the diameter.

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int d, D, s, M, n;
static int *mul, *inv_t;
static int *sig, *sinv, *G, *nbr, *dist, *queue;
static long cur;
static u64 rs = 88172645463325252ULL;
static clock_t t0;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int m) {
    return (int)(rnd64() % (u64)m);
}

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static void build_col(int kk) {
    int i, j, x, y, g, ig;
    for (i = 0; i < s; i++) {
        j = sig[kk * s + i];
        g = G[kk * s + i];
        for (x = 0; x < M; x++)
            nbr[(i * M + x) * d + kk] = s * M + j * M + mul[x * M + g];
    }
    for (j = 0; j < s; j++) {
        i = sinv[kk * s + j];
        g = G[kk * s + i];
        ig = inv_t[g];
        for (y = 0; y < M; y++)
            nbr[(s * M + j * M + y) * d + kk] = i * M + mul[y * M + ig];
    }
}

static void swap_sig(int kk, int a, int b) {
    int *p = sig + kk * s;
    int *q = sinv + kk * s;
    int t = p[a];
    p[a] = p[b];
    p[b] = t;
    q[p[a]] = a;
    q[p[b]] = b;
}

/* Number of (orbit representative, vertex) pairs at distance > D. Zero iff valid. */
static long cost(void) {
    int srcs[16];
    int ns = 0, i, j, t, qh, qt, v, kk;
    long bad = 0;
    for (i = 0; i < s; i++) srcs[ns++] = i * M;
    for (j = 0; j < s; j++) srcs[ns++] = s * M + j * M;
    for (t = 0; t < ns; t++) {
        for (v = 0; v < n; v++) dist[v] = -1;
        dist[srcs[t]] = 0;
        qh = 0;
        qt = 0;
        queue[qt++] = srcs[t];
        while (qh < qt) {
            v = queue[qh++];
            if (dist[v] >= D) continue;
            for (kk = 0; kk < d; kk++) {
                int u = nbr[v * d + kk];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    queue[qt++] = u;
                }
            }
        }
        bad += n - qt;
    }
    return bad;
}

int main(int argc, char **argv) {
    int nn, mm, i, L, v, kk, found = 0;
    int *buf;
    double budget;
    unsigned long long seedv;
    const int STEPS = 3000;

    if (argc < 7) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    s = atoi(argv[3]);
    M = atoi(argv[4]);
    seedv = strtoull(argv[5], NULL, 10);
    budget = atof(argv[6]);
    if (d < 1 || d > 32 || D < 1 || s < 1 || s > 8 || M < 2 || M > 400) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (u64)seedv * 2654435761ULL + 12345ULL;
    if (rs == 0) rs = 1;

    if (scanf("%d %d", &nn, &mm) != 2 || mm < 0) { printf("0 0\n"); return 0; }
    (void)nn;
    L = 2 * mm;
    if (L < 1 + M * M + M) { printf("0 0\n"); return 0; }
    buf = malloc(sizeof(int) * (size_t)L);
    if (!buf) { printf("0 0\n"); return 0; }
    for (i = 0; i < L; i++)
        if (scanf("%d", &buf[i]) != 1) { printf("0 0\n"); return 0; }
    if (buf[0] != M) { printf("0 0\n"); return 0; }
    mul = buf + 1;
    inv_t = buf + 1 + M * M;

    n = 2 * s * M;
    sig = malloc(sizeof(int) * (size_t)(s * d));
    sinv = malloc(sizeof(int) * (size_t)(s * d));
    G = malloc(sizeof(int) * (size_t)(s * d));
    nbr = malloc(sizeof(int) * (size_t)(n * d));
    dist = malloc(sizeof(int) * (size_t)n);
    queue = malloc(sizeof(int) * (size_t)n);
    if (!sig || !sinv || !G || !nbr || !dist || !queue) { printf("0 0\n"); return 0; }

    t0 = clock();
    while (!found && elapsed() < budget) {
        int step;
        for (kk = 0; kk < d; kk++) {
            for (i = 0; i < s; i++) sig[kk * s + i] = i;
            for (i = s - 1; i > 0; i--) {
                int r = rnd(i + 1);
                int t = sig[kk * s + i];
                sig[kk * s + i] = sig[kk * s + r];
                sig[kk * s + r] = t;
            }
            for (i = 0; i < s; i++) sinv[kk * s + sig[kk * s + i]] = i;
            for (i = 0; i < s; i++) G[kk * s + i] = rnd(M);
            build_col(kk);
        }
        cur = cost();
        for (step = 0; step < STEPS && cur > 0; step++) {
            double T, frac;
            long c;
            if ((step & 15) == 0 && elapsed() > budget) break;
            frac = (double)step / (double)STEPS;
            T = 1.5 * (1.0 - frac) + 0.05;
            kk = rnd(d);
            if (s == 1 || rnd(10) < 7) {
                int ii = rnd(s);
                int old = G[kk * s + ii];
                int nw = rnd(M);
                if (nw == old) continue;
                G[kk * s + ii] = nw;
                build_col(kk);
                c = cost();
                if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
                    cur = c;
                } else {
                    G[kk * s + ii] = old;
                    build_col(kk);
                }
            } else {
                int a = rnd(s), b = rnd(s);
                if (a == b) continue;
                swap_sig(kk, a, b);
                build_col(kk);
                c = cost();
                if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
                    cur = c;
                } else {
                    swap_sig(kk, a, b);
                    build_col(kk);
                }
            }
        }
        if (cur == 0) found = 1;
    }

    if (found) {
        int V = s * M;
        printf("%d %d\n", 2 * V, V * d);
        for (v = 0; v < V; v++)
            for (kk = 0; kk < d; kk++)
                printf("%d %d\n", v, nbr[v * d + kk]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ---------------------------------------------------------------- groups

def _group_table(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k, element (a,b) coded a*k+b, identity 0."""
    M = m * k
    pw = [pow(r, b, m) for b in range(k)]
    tab = [[0] * M for _ in range(M)]
    for x in range(M):
        a, b = divmod(x, k)
        row = tab[x]
        for y in range(M):
            c, dd = divmod(y, k)
            row[y] = ((a + pw[b] * c) % m) * k + (b + dd) % k
    inv = []
    for x in range(M):
        a, b = divmod(x, k)
        nb = (-b) % k
        inv.append(((-pw[nb] * a) % m) * k + nb)
    return tab, inv


def _presentations(M, rng, limit):
    """Semidirect presentations (m, k, r) with m*k = M: cyclic first, then random nonabelian ones."""
    out = [(M, 1, 1)]
    ks = [k for k in range(2, 9) if M % k == 0 and M // k >= 2]
    rng.shuffle(ks)
    for k in ks:
        m = M // k
        cands = [m - 1] if k == 2 else []
        for _ in range(60):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                cands.append(r)
        if cands:
            out.append((m, k, rng.choice(cands)))
    return out[:limit]


# ---------------------------------------------------------------- algebraic bases

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX), or None."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (degree q+1 <= d)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- lift search

def _run_lift(d, D, s, M, pres, seedv, budget):
    """Run the C annealer for one (s, group) pair. Returns a verified (n, edges) or None."""
    m, k, r = pres
    tab, inv = _group_table(m, k, r)
    flat = [M]
    for row in tab:
        flat.extend(row)
    flat.extend(inv)
    if len(flat) % 2:
        flat.append(0)
    pairs = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
    try:
        text = lib.run_c(C_SOURCE, [d, D, s, M, seedv, round(budget, 2)],
                         stdin_graph=(1, pairs), timeout=budget + 5.0)
        n, edges = lib.parse_graph_text(text)
    except Exception:
        return None
    if n < 2 or not edges:
        return None
    ed = sorted({(min(u, v), max(u, v)) for u, v in edges})
    if lib.is_valid(n, ed, d, D):
        return (n, ed)
    return None


def _try_T(T, d, D, seed, rng, budget):
    """Try to realise a valid lift on 2T vertices over all (s, group) splits of T."""
    combos = []
    for s in S_LIST:
        if T % s:
            continue
        M = T // s
        if M < 2 or M > MAXM:
            continue
        for pres in _presentations(M, rng, PRES_PER_ORDER):
            combos.append((s, M, pres))
    if not combos or budget < 0.1:
        return None
    per = budget / len(combos)
    for idx, (s, M, pres) in enumerate(combos):
        res = _run_lift(d, D, s, M, pres, seed * 1000 + T * 7 + idx, per)
        if res is not None:
            return res
    return None


def _lift_search(d, D, seed, rng, end, base_n, consider):
    """Bisection over the half-order T for the largest T with a valid lift."""
    moore = lib._moore_bound(d, D)
    Tmax = min(moore // 2, TCAP)
    lo, hi = base_n // 2, Tmax + 1
    if lo >= Tmax:
        return
    while hi - lo > 1:
        rem = end - time.monotonic()
        if rem < 0.8:
            return
        mid = (lo + hi) // 2
        budget = min(LIFT_MAX_BUDGET, max(0.8, LIFT_FRAC * rem))
        res = _try_T(mid, d, D, seed, rng, budget)
        if res is not None:
            consider(res)
            lo = mid
        else:
            hi = mid
    rem = end - time.monotonic()
    if hi <= Tmax and rem > 1.0:
        res = _try_T(hi, d, D, seed, rng, rem * 0.9)
        if res is not None:
            consider(res)


# ---------------------------------------------------------------- driver

def _trivial(d, D):
    """Always-valid fallback graph."""
    if d < 1 or D < 1:
        return (1, [])
    if d == 1 or D == 1:
        return (2, [(0, 1)])
    if d == 2:
        L = 2 * D
        return (L, [(i, (i + 1) % L) for i in range(L)])
    return lib.haar_graph(d, range(d))


def _build_inner(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(1.0, TIME_FRAC * time_limit - 1.0)
    rng = random.Random(seed * 1000003 + 97 * d + D)
    best = [_trivial(d, D)]

    def consider(c):
        if c is None:
            return
        if c[0] > best[0][0] and lib.is_valid(c[0], c[1], d, D):
            best[0] = c

    if D == 3 and lib.is_prime_power(d - 1):
        consider(lib.projective_plane_incidence(d - 1))
        return best[0]
    if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
        consider(_gq_w(d - 1))
        return best[0]

    if D == 3:
        try:
            consider(_pg_base(d))
        except Exception:
            pass
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    elif D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if d <= 32:
        _lift_search(d, D, seed, rng, end, best[0][0], consider)
    return best[0]


def build(d, D, seed, time_limit):
    if d <= 2 or D <= 2:
        return _trivial(d, D)
    try:
        res = _build_inner(d, D, seed, time_limit)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            return res
    except Exception:
        pass
    return _trivial(d, D)

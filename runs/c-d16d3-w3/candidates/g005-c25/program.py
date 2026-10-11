"""Arc-extended projective plane graphs (diameter 3) with C-side packing search.

Start from the incidence graph of PG(2, q), with points 0..m-1 and lines m..2m-1.
Each old vertex has degree q+1, so it has spare s = d - q - 1.

A-side: choose a multiset of points. Each chosen point gets a new vertex joined to
its q+1 lines. Every line may receive at most s new edges.
B-side: choose a multiset of lines. Each chosen line gets a new vertex joined to
its q+1 points. Every point may receive at most s new edges.

The two sides are independent packing problems, solved by simulated annealing in C.
Repeats are allowed, so the LP bound is floor(s*m/(q+1)) per side. Diameter stays 3
for any such multisets. Every output is still checked with lib.is_valid.

Fallbacks: a greedy Python packing on the same PG graph, K_{d,d} for D = 2, and
W(q) for D >= 4.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rng_s = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int N, E, half, S_CAP, QQ;
static int *deg, *off, *nb;
static int *cnt, *load, *bestc, *final_c;
static int total, over, RES_SHIFT;
static const double LAM = 1.4;

/* Add dlt (+1 or -1) to item vertex v. Returns the change in overflow. */
static int apply_item(int v, int dlt) {
    int dov = 0;
    for (int k = off[v]; k < off[v + 1]; k++) {
        int r = nb[k] - RES_SHIFT;
        if (dlt > 0) {
            if (load[r] >= S_CAP) dov++;
            load[r]++;
        } else {
            load[r]--;
            if (load[r] >= S_CAP) dov--;
        }
    }
    cnt[v] += dlt;
    total += dlt;
    over += dov;
    return dov;
}

/* Maximise the number of chosen items (with repeats) subject to load <= S_CAP on every
   resource. Items are vertices base..base+nitems-1. Resource of neighbour x is x - shift.
   Returns the best feasible total; bestc holds the counts. */
static int pack_side(int base, int shift, int nitems, double t_end) {
    RES_SHIFT = shift;
    memset(bestc, 0, sizeof(int) * (size_t)N);
    int best_total = 0;
    double span = t_end - now_sec();
    if (span <= 0.0) return 0;
    double rl = span / 5.0;
    if (rl < 0.3) rl = 0.3;

    for (;;) {
        double rs = now_sec();
        if (rs >= t_end - 1e-3) break;
        double re = rs + rl;
        if (re > t_end) re = t_end;

        for (int v = base; v < base + nitems; v++) cnt[v] = 0;
        memset(load, 0, sizeof(int) * (size_t)half);
        total = 0;
        over = 0;

        double T0 = 0.8, T1 = 0.02, T = T0;
        unsigned long long it = 0;
        for (;;) {
            if ((it & 1023ULL) == 0ULL) {
                double now = now_sec();
                if (now >= re) break;
                double f = (now - rs) / (re - rs);
                T = T0 * pow(T1 / T0, f);
            }
            it++;
            if (rnd01() < 0.3) {
                /* single +1 or -1 move */
                int v = base + rndint(nitems);
                int dlt = (cnt[v] == 0 || rnd01() < 0.6) ? 1 : -1;
                int ot = total;
                int dov = apply_item(v, dlt);
                double dF = (double)(total - ot) - LAM * (double)dov;
                if (dF < 0.0 && rnd01() >= exp(dF / T)) apply_item(v, -dlt);
            } else {
                /* swap move: +1 on v, -1 on a chosen item u */
                int v = base + rndint(nitems);
                int u = -1;
                for (int t = 0; t < 8; t++) {
                    int w = base + rndint(nitems);
                    if (w != v && cnt[w] > 0) { u = w; break; }
                }
                if (u < 0) continue;
                int dov1 = apply_item(v, 1);
                int dov2 = apply_item(u, -1);
                double dF = -LAM * (double)(dov1 + dov2);
                if (dF < 0.0 && rnd01() >= exp(dF / T)) {
                    apply_item(u, 1);
                    apply_item(v, -1);
                    continue;
                }
            }
            if (over == 0 && total > best_total) {
                best_total = total;
                for (int w = base; w < base + nitems; w++) bestc[w] = cnt[w];
            }
        }
    }
    return best_total;
}

static void echo_input(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double t_start = now_sec();

    rng_s ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rng_s == 0) rng_s = 1;
    rnd64();
    rnd64();

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) { n_in = 0; m_in = 0; }
    if (m_in < 0) m_in = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m_in + 1));
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m_in = i; break; }
    }

    if (n_in <= 0 || (n_in & 1)) {
        echo_input(n_in > 0 ? n_in : 0, 0, eu, ev);
        return 0;
    }
    half = n_in / 2;
    QQ = 0;
    for (int q = 1; q * q + q + 1 <= half; q++) {
        if (q * q + q + 1 == half) { QQ = q; break; }
    }
    int bip_ok = 1;
    for (int i = 0; i < m_in; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n_in || b >= n_in) { bip_ok = 0; break; }
        if ((a < half) == (b < half)) { bip_ok = 0; break; }
    }
    if (QQ == 0 || D < 3 || !bip_ok || d - (QQ + 1) <= 0) {
        echo_input(n_in, m_in, eu, ev);
        return 0;
    }

    S_CAP = d - (QQ + 1);
    N = n_in;
    E = m_in;
    deg = calloc((size_t)N, sizeof(int));
    for (int i = 0; i < E; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    off = malloc(sizeof(int) * (size_t)(N + 1));
    off[0] = 0;
    for (int v = 0; v < N; v++) off[v + 1] = off[v] + deg[v];
    nb = malloc(sizeof(int) * (size_t)(2 * E + 1));
    int *pos = malloc(sizeof(int) * (size_t)(N + 1));
    memcpy(pos, off, sizeof(int) * (size_t)(N + 1));
    for (int i = 0; i < E; i++) {
        nb[pos[eu[i]]++] = ev[i];
        nb[pos[ev[i]]++] = eu[i];
    }
    free(pos);

    cnt = calloc((size_t)N, sizeof(int));
    bestc = calloc((size_t)N, sizeof(int));
    final_c = calloc((size_t)N, sizeof(int));
    load = calloc((size_t)half + 1, sizeof(int));

    double end_all = t_start + budget;
    double endA = t_start + 0.5 * budget;

    /* A side: items are points 0..half-1, resources are lines (index nb - half). */
    pack_side(0, half, half, endA);
    for (int v = 0; v < half; v++) final_c[v] = bestc[v];

    /* B side: items are lines half..N-1, resources are points (index nb). */
    pack_side(half, 0, half, end_all);
    for (int v = half; v < N; v++) final_c[v] = bestc[v];

    long long extra = 0, addE = 0;
    for (int v = 0; v < N; v++) {
        if (final_c[v] > 0) {
            extra += final_c[v];
            addE += (long long)final_c[v] * deg[v];
        }
    }
    printf("%lld %lld\n", (long long)N + extra, (long long)E + addE);
    for (int i = 0; i < E; i++) printf("%d %d\n", eu[i], ev[i]);
    int nxt = N;
    for (int v = 0; v < N; v++) {
        for (int c = 0; c < final_c[v]; c++) {
            int x = nxt++;
            for (int k = off[v]; k < off[v + 1]; k++) printf("%d %d\n", x, nb[k]);
        }
    }
    return 0;
}
"""


def _pg_candidates(d):
    """(estimated order, q, spare s) for each prime power q with q + 1 <= d, best estimate first."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        m = q * q + q + 1
        s = d - q - 1
        out.append((2 * m + 2 * (s * m // (q + 1)), q, s))
    out.sort(reverse=True)
    return out


def _py_greedy(q, d):
    """Pure-Python fallback: greedy sets on each side of PG(2, q) with capacity s = d - q - 1."""
    n0, e0 = lib.projective_plane_incidence(q)
    m = n0 // 2
    s = d - q - 1
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in e0:
        pl[u].append(v - m)
        lp[v - m].append(u)

    def side(nbr):
        load = [0] * m
        chosen = []
        for x in range(m):
            if all(load[t] < s for t in nbr[x]):
                chosen.append(x)
                for t in nbr[x]:
                    load[t] += 1
        return chosen

    SA = side(pl)
    SB = side(lp)
    n = n0
    E = list(e0)
    for P in SA:
        x = n
        n += 1
        E += [(x, m + L) for L in pl[P]]
    for j in SB:
        x = n
        n += 1
        E += [(x, Q) for Q in lp[j]]
    return n, E


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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is a valid fallback for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _pg_candidates(d)
        if cands:
            _, q0, _ = cands[0]
            consider(*lib.projective_plane_incidence(q0))
            try:
                consider(*_py_greedy(q0, d))
            except (ValueError, RuntimeError):
                pass

            runs = [(est, q, s) for est, q, s in cands if s >= 1][:2]
            limit = 0.8 * time_limit
            fracs = [0.7, 1.0]
            for (est, q, s), fr in zip(runs, fracs):
                elapsed = time.monotonic() - t0
                budget = max(0.5, fr * (limit - elapsed))
                if elapsed + budget > limit + 0.1 * time_limit:
                    break
                n0, e0 = lib.projective_plane_incidence(q)
                try:
                    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                    stdin_graph=(n0, e0), timeout=budget + 5.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
                except (RuntimeError, ValueError):
                    pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

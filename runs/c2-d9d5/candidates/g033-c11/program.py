"""Two-orbit voltage lifts over a wider family of groups, with a Python-driven climb.

New in this version:
  * Group family. Besides the affine groups F_q x| C_c used before, the candidates now include
    semidirect products Z_m x|_r Z_k (r^k = 1 mod m), which covers cyclic (k = 1), dihedral
    (k = 2, r = -1), and direct-product cases. Python enumerates them, and C builds the full
    multiplication table, so one C engine handles every group type.
  * Climb over group orders. Python bisects over the sorted candidate list for the largest group
    order the engine can cover, with a second pass over the remaining orders. Stage A uses K = 2
    left and K = 2 right orbits (4|G| vertices). Stage B uses K = 1 (2|G| vertices).

Each probe is one C run on one group. The C engine runs simulated annealing on dart targets and
voltages and prints a graph only when every orbit representative reaches all vertices within D
steps. Left translation is an automorphism for any group, so 2K BFS runs decide the diameter.
The best valid graph wins. Python validates every returned graph with lib.is_valid.
"""
import itertools
import random
import time

import lib

MAX_N = 3000  # must match MAXN in the C source

C_SOURCE = r'''
/* Two-orbit voltage lift search over an arbitrary explicit group family.
 * Usage: prog d D seed budget K kind par...
 *   kind 0: affine group F_q x| C_c         par = q c
 *   kind 1: semidirect Z_m x|_r Z_k         par = m k r
 * Output: "n m" then m lines "u v" for a valid graph, or "0 0".
 * Vertices: left L^a_x = a*GN + x (a < K); right R^b_y = K*GN + b*GN + y.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXN 3000
#define MAXD 32
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)

static int K, d, D, GN, nd;
static int *MT = NULL; /* MT[x*GN + y] = x*y */
static int *IV = NULL; /* IV[x] = x^-1 */
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

/* ------------------------------------------------------------ group tables */

static void fill_inverse(void) {
    IV = malloc(sizeof(int) * (size_t)GN);
    for (int x = 0; x < GN; x++) {
        IV[x] = 0;
        for (int y = 0; y < GN; y++)
            if (MT[x * GN + y] == 0) { IV[x] = y; break; }
    }
}

static static_int_dummy_unused;

static int setup_affine(int q, int c) {
    int p, k;
    if (q < 3 || q >= MAXQ || !factor_pp(q, &p, &k)) return 0;
    if (c < 1 || c >= q || (q - 1) % c) return 0;
    if ((long)q * c > MAXN) return 0;
    build_field(q, p, k);
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (g < 0) return 0;
    static int PWG[MAXQ], Hel[MAXQ], hidx[MAXQ];
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    /* Element (a, h_j) is coded a*c + j; (a,h_j)(b,h_t) = (a + h_j b, h_j h_t). */
    GN = q * c;
    MT = malloc(sizeof(int) * (size_t)GN * (size_t)GN);
    for (int x = 0; x < GN; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < GN; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[Hel[j]][b]];
            int nj = hidx[MULT[Hel[j]][Hel[t]]];
            MT[x * GN + y] = na * c + nj;
        }
    }
    fill_inverse();
    return 1;
}

static int mulmod_pow(int r, int k, int m) {
    long long res = 1 % m, b = r % m;
    int e = k;
    while (e > 0) {
        if (e & 1) res = res * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)res;
}

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c, b + e). */
static int setup_semi(int m, int k, int r) {
    if (m < 2 || k < 1 || r < 0 || r >= m) return 0;
    if (mulmod_pow(r, k, m) != 1) return 0;
    if ((long)m * k > MAXN) return 0;
    GN = m * k;
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (pw[b - 1] * r) % m;
    MT = malloc(sizeof(int) * (size_t)GN * (size_t)GN);
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, e = y % k;
            int na = (a + pw[b] * c) % m;
            int nb = (b + e) % k;
            MT[x * GN + y] = na * k + nb;
        }
    }
    fill_inverse();
    return 1;
}

/* ------------------------------------------------------------ voltage lift state */

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN]; /* x*g and x*g^-1 for dart t */
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart t leaves left orbit a = t/d: L^a_x ~ R^{tb[t]}_{x * vg[t]}. */
static void set_dart(int t, int x) {
    vg[t] = x;
    int ix = IV[x];
    for (int g = 0; g < GN; g++) {
        fwdT[t][g] = MT[g * GN + x];
        invT[t][g] = MT[g * GN + ix];
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

static void random_init(void) {
    int list[MAXND];
    int p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i]; list[i] = list[j]; list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GN));
}

static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

static int bfs_count(int src) {
    int V2 = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / GN, x = v % GN;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * GN + fwdT[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - V2;
                int b = w / GN, y = w % GN;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * GN + invT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms transitive on each orbit, so one BFS per
 * orbit representative decides the diameter. */
static long cover_cost(void) {
    long V = 2L * K * GN;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * GN + b * GN);
    return c + 1000L * dup_count();
}

static int search_group(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            long c2;
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                rebuild_inc();
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd);
                int x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int V = 2 * K * GN;
    printf("%d %d\n", V, K * GN * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * GN + tb[t] * GN + fwdT[t][x];
                printf("%d %d\n", a * GN + x, u);
            }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    K = atoi(argv[5]);
    int kind = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + budget * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    nd = K * d;

    int ok = 0;
    if (kind == 0 && argc >= 9) ok = setup_affine(atoi(argv[7]), atoi(argv[8]));
    else if (kind == 1 && argc >= 10) ok = setup_semi(atoi(argv[7]), atoi(argv[8]), atoi(argv[9]));
    if (!ok || GN < 2 || GN > MAXN) {
        printf("0 0\n");
        return 0;
    }

    if (search_group(t_end)) print_result();
    else printf("0 0\n");
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


def _group_candidates(lo, hi, seed, max_k=8):
    """Sorted (order, kind, params) candidates with order in [lo, hi].

    kind 0: affine F_q x| C_c. kind 1: semidirect Z_m x|_r Z_k with r^k = 1 mod m
    (r = 1 gives the direct product, r = m-1 with k even gives dihedral-type groups).
    """
    lo = max(lo, 2)
    if hi < lo:
        return []
    rng = random.Random(1000 + seed)
    out = set()
    for q in range(3, 256):
        if not lib.is_prime_power(q):
            continue
        for c in range(2, q):
            if (q - 1) % c == 0 and lo <= q * c <= hi:
                out.add((q * c, 0, (q, c)))
    for k in range(1, max_k + 1):
        m_lo = max(2, -(-lo // k))
        m_hi = hi // k
        for m in range(m_lo, m_hi + 1):
            rs = {1}
            if k % 2 == 0 and m > 2:
                rs.add(m - 1)
            if m > 2:
                for _ in range(20):
                    r = rng.randrange(2, m)
                    if pow(r, k, m) == 1:
                        rs.add(r)
            for r in rs:
                out.add((m * k, 1, (m, k, r)))
    return sorted(out)


def _probe(d, D, seed, K, cand, budget):
    """One C run on one group. Returns (n, edges) or None."""
    N, kind, par = cand
    args = [d, D, seed, round(budget, 2), K, kind, *par]
    text = lib.run_c(C_SOURCE, args, stdin_graph=None, timeout=budget + 8.0)
    n, edges = lib.parse_graph_text(text)
    if n <= 0 or not edges:
        return None
    return n, edges


def _climb(d, D, seed, K, cands, budget, consider):
    """Bisect over sorted candidate groups for the largest feasible order, then scan upward."""
    if not cands or budget < 3.0:
        return
    t_stop = time.monotonic() + budget

    def rem():
        return t_stop - time.monotonic()

    def probe(i, sl):
        try:
            res = _probe(d, D, seed * 997 + 31 * i + K, K, cands[i], sl)
        except Exception:
            return False
        return consider(res)

    lo_i, hi_i = 0, len(cands) - 1
    while lo_i <= hi_i and rem() > 3.0:
        mid = (lo_i + hi_i) // 2
        sl = min(rem() - 1.0, max(2.5, 0.25 * rem()))
        if probe(mid, sl):
            lo_i = mid + 1
        else:
            hi_i = mid - 1

    idx, fails = lo_i, 0
    while idx < len(cands) and rem() > 3.0 and fails < 2:
        sl = min(rem() - 1.0, max(2.5, 0.5 * rem()))
        if probe(idx, sl):
            fails = 0
        else:
            fails += 1
        idx += 1


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return False
        n, e = cand
        if not lib.is_valid(n, e, d, D):
            return False
        if n > best[0]:
            best = (n, e)
        return True

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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        # Stage A: two left and two right orbits, n = 4|G|, with |G| in (best/4, mb/4].
        T = left() - 6.0
        lo = best[0] // 4 + 1
        hi = mb // 4
        if T > 6.0 and lo <= hi:
            cands = _group_candidates(lo, hi, seed)
            _climb(d, D, seed, 2, cands, 0.55 * T, consider)

        # Stage B: one left and one right orbit, n = 2|G|, with the remaining time.
        T = left() - 4.0
        lo = best[0] // 2 + 1
        hi = min(mb // 2, MAX_N)
        if T > 4.0 and lo <= hi:
            cands = _group_candidates(lo, hi, seed + 1)
            _climb(d, D, seed + 1, 1, cands, T, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

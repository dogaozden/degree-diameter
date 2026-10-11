"""Bold variant: abelian bi-Cayley lifts over arbitrary abelian groups (any rank, not only
metacyclic), with one or two base vertices per side. The C engine runs iterative-deepening
hill-climbs on dart voltages, orbit-reduced: by translation symmetry, only the 2p fibre
representatives need a BFS. Python keeps the algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez,
K_{d,d}) as the fallback and accepts the C result only if lib.is_valid confirms it."""
import time

import itertools

import lib

C_SOURCE = r'''
/* Abelian voltage lifts with p = 1 or 2 base vertices per side.
 * Usage: prog d D seed time_limit baseline_n     (stdin ignored)
 * Output: "n m" plus edges of the best valid graph with n > baseline_n, or "0 0".
 *
 * Group: Z_m1 x ... x Z_mk (any rank), elements indexed in mixed radix.
 * Lift: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins A(i,x) to B(j, x+g). Base is d-regular on p+p vertices.
 * Validity: BFS from the 2p fibre representatives only (translation symmetry).
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXV 2048
#define MAXDEG 32
#define MAXE 40000
#define MAXDARTS 64
#define MAXGROUPS 512

static int d, D;
static double t_end;
static long moore;

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

/* ---------------- abelian group tables ---------------- */
static int G_N, G_k, G_mod[10];
static int G_comp[MAXG][10];
static int G_add[MAXG][MAXG];

static void set_group(const int *mods, int k) {
    G_k = k;
    G_N = 1;
    for (int t = 0; t < k; t++) {
        G_mod[t] = mods[t];
        G_N *= mods[t];
    }
    for (int x = 0; x < G_N; x++) {
        int r = x;
        for (int t = 0; t < k; t++) {
            G_comp[x][t] = r % G_mod[t];
            r /= G_mod[t];
        }
    }
    for (int x = 0; x < G_N; x++)
        for (int y = 0; y < G_N; y++) {
            int z = 0, stride = 1;
            for (int t = 0; t < k; t++) {
                int c = (G_comp[x][t] + G_comp[y][t]) % G_mod[t];
                z += c * stride;
                stride *= G_mod[t];
            }
            G_add[x][y] = z;
        }
}

static int gl_mods[MAXGROUPS][10], gl_k[MAXGROUPS], gl_n;

static void gen_fact(int rem, int minf, int *cur, int k) {
    if (rem == 1) {
        if (k > 0 && gl_n < MAXGROUPS) {
            memcpy(gl_mods[gl_n], cur, sizeof(int) * k);
            gl_k[gl_n++] = k;
        }
        return;
    }
    if (k >= 9) return;
    for (int f = minf; f <= rem; f++)
        if (rem % f == 0) {
            cur[k] = f;
            gen_fact(rem / f, f, cur, k + 1);
        }
}

static void groups_of_order(int N) {
    int cur[10];
    gl_n = 0;
    if (N >= 2) gen_fact(N, 2, cur, 0);
}

/* ---------------- lift state ---------------- */
static int P_, NN_;
static int M_[2][2];
static int nd;
static int dA[MAXDARTS], dB[MAXDARTS], dg[MAXDARTS];
static int V_;
static int adj[MAXV][MAXDEG], deg_[MAXV];
static int dist_[MAXV], que_[MAXV];

static int best_n = 0;
static int have_best = 0;
static int out_n = 0, out_m = 0;
static int eu[MAXE], ev[MAXE];

static int fresh_volt(int t) {
    for (;;) {
        int g = rndint(NN_), ok = 1;
        for (int s = 0; s < nd; s++)
            if (s != t && dg[s] == g && dA[s] == dA[t] && dB[s] == dB[t]) {
                ok = 0;
                break;
            }
        if (ok) return g;
    }
}

static void build(void) {
    V_ = 2 * P_ * NN_;
    for (int v = 0; v < V_; v++) deg_[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NN_; x++) {
            int a = dA[t] * NN_ + x;
            int b = (P_ + dB[t]) * NN_ + G_add[x][dg[t]];
            adj[a][deg_[a]++] = b;
            adj[b][deg_[b]++] = a;
        }
}

/* Number of (representative, vertex) pairs at distance > D. Zero means valid lift. */
static long eval(void) {
    build();
    long bad = 0;
    for (int r = 0; r < 2 * P_; r++) {
        int src = r * NN_;
        for (int v = 0; v < V_; v++) dist_[v] = -1;
        int h = 0, tl = 0;
        dist_[src] = 0;
        que_[tl++] = src;
        while (h < tl) {
            int v = que_[h++];
            if (dist_[v] >= D) continue;
            for (int i = 0; i < deg_[v]; i++) {
                int u = adj[v][i];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    que_[tl++] = u;
                }
            }
        }
        bad += V_ - tl;
    }
    return bad;
}

static void random_base(void) {
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) M_[i][j] = 0;
    if (P_ == 1) {
        M_[0][0] = d;
    } else {
        /* connected d-regular 2+2 base: s swaps, d-s identities, 1 <= s <= d-1 */
        int s = 1 + rndint(d - 1);
        M_[0][1] = M_[1][0] = s;
        M_[0][0] = M_[1][1] = d - s;
    }
}

static int setup_darts(void) {
    nd = 0;
    for (int i = 0; i < P_; i++)
        for (int j = 0; j < P_; j++)
            for (int c = 0; c < M_[i][j]; c++) {
                if (nd >= MAXDARTS) return 0;
                dA[nd] = i;
                dB[nd] = j;
                dg[nd] = -1;
                nd++;
            }
    for (int t = 0; t < nd; t++) dg[t] = fresh_volt(t);
    return 1;
}

static long climb(long steps) {
    long bad = eval();
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) break;
        int t = rndint(nd);
        int old = dg[t];
        dg[t] = fresh_volt(t);
        long nb = eval();
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dg[t] = old;
    }
    return bad;
}

static void save_best(void) {
    eval();
    out_n = V_;
    out_m = 0;
    for (int v = 0; v < V_; v++)
        for (int i = 0; i < deg_[v]; i++) {
            int u = adj[v][i];
            if (v < u && out_m < MAXE) {
                eu[out_m] = v;
                ev[out_m] = u;
                out_m++;
            }
        }
    best_n = V_;
    have_best = 1;
}

static int try_group(int p, int N, long steps, int tries) {
    P_ = p;
    NN_ = N;
    for (int tr = 0; tr < tries && now() < t_end; tr++) {
        if (2L * p * N <= best_n) return 0;
        random_base();
        for (int i = 0; i < P_; i++)
            for (int j = 0; j < P_; j++)
                if (M_[i][j] > N) return 0;
        if (!setup_darts()) return 0;
        if (climb(steps) == 0) {
            save_best();
            return 1;
        }
    }
    return 0;
}

/* One pass over all eligible (p, N, group) with the given effort.
 * Returns the number of group attempts made (0 means nothing eligible). */
static int sweep(long steps, int tries) {
    int work = 0;
    for (int N = 2; N <= MAXG && now() < t_end; N++) {
        for (int p = 1; p <= 2; p++) {
            long total = 2L * p * N;
            if (total <= best_n || total > moore || total > MAXV) continue;
            if (p == 2 && d < 2) continue;
            groups_of_order(N);
            for (int gi = 0; gi < gl_n && now() < t_end; gi++) {
                if (2L * p * N <= best_n) break;
                set_group(gl_mods[gi], gl_k[gi]);
                work++;
                try_group(p, N, steps, tries);
            }
        }
    }
    return work;
}

static long moore_cap(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    best_n = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    moore = moore_cap();

    long steps = 600;
    int tries = 2;
    while (now() < t_end) {
        int work = sweep(steps, tries);
        if (work == 0) break;
        if (steps < 20000000L) steps *= 3;
        tries++;
    }

    if (have_best) {
        printf("%d %d\n", out_n, out_m);
        for (int i = 0; i < out_m; i++) printf("%d %d\n", eu[i], ev[i]);
    } else {
        printf("0 0\n");
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

    # Safe fallback: K_{d,d} (diameter 2), then the best algebraic construction.
    best = lib.haar_graph(d, range(d))
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 15)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best

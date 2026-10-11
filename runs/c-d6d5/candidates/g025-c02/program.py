import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley / voltage lifts over an ARBITRARY finite group given by
# its multiplication table (supplied by Python). The old engine could only use
# semidirect products Z_m x| Z_k. Here the groups are affine groups
# F_q x| H (H a subgroup of F_q^*), dihedral groups, cyclic groups and small
# direct products. Each run picks a group G and a base size K in 1..4, and
# uses simulated annealing with breakout weights to find layer-permutation
# voltages s in G. Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart
# (i, j, s) joins A_i,g to B_j,g*s. Left multiplication is an automorphism,
# so diameter <= D iff BFS of depth D from each of the 2K block representatives
# (vertex r*G, the identity of the group) covers the whole graph.
# Every output is re-checked in Python with lib.is_valid before it is kept.
#
# Input (stdin, read as a flat integer stream after the "n m" header from
# lib.graph_to_text): ng, then for each group: G followed by its G*G table
# entries, row-major, with identity at index 0.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXK 4
#define MAXNG 512
#define ITERS 15000
#define BRK 200

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM;
static int ng = 0;
static int gord[MAXNG];
static int *gtab[MAXNG];
static int maxG = 0;
static int NMAX = 0;

static int K, G, T, N;
static const int *MUL;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static int curstamp = 0;
static long long *wt, *unc;
static long long sumw = 0;
static long long last_w = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static void alloc_all(void) {
    int Tm = DEG * MAXK;
    NMAX = 2 * MAXK * maxG;
    dI = malloc(sizeof(int) * (size_t)Tm);
    dJ = malloc(sizeof(int) * (size_t)Tm);
    dS = malloc(sizeof(int) * (size_t)Tm);
    bestJ = malloc(sizeof(int) * (size_t)Tm);
    bestS = malloc(sizeof(int) * (size_t)Tm);
    perm = malloc(sizeof(int) * (size_t)Tm * (size_t)maxG);
    adj = malloc(sizeof(int) * (size_t)NMAX * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)NMAX);
    stamp = calloc((size_t)NMAX, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NMAX);
    nx = malloc(sizeof(int) * (size_t)NMAX);
    wt = malloc(sizeof(long long) * 2 * MAXK);
    unc = malloc(sizeof(long long) * 2 * MAXK);
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = MUL[(size_t)g * G + s];
}

/* Returns the true cost (sum of uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    int NB = 2 * K;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < NB; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            if (cnt[a] < DEG && cnt[b] < DEG) {
                adj[(size_t)a * DEG + cnt[a]++] = b;
                adj[(size_t)b * DEG + cnt[b]++] = a;
            }
        }
    }
    /* Pad unused slots with self-loops so BFS never reads stale data. */
    for (int v = 0; v < N; v++)
        for (int e = cnt[v]; e < DEG; e++) adj[(size_t)v * DEG + e] = v;

    long long total = 0;
    for (int r = 0; r < NB; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NMAX);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int src = r * G;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = N - count;
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < NB; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Annealing on the weighted cost with breakout weight bumps.
   Best state (by true cost) goes to bestJ/bestS. */
static long long run_sa(int iters, double tscale, long long cost) {
    int NB = 2 * K;
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < NB; r++)
                    if (unc[r] > 0) { wt[r]++; sumw++; }
                wcur = 0;
                for (int r = 0; r < NB; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double avgw = (double)sumw / (double)NB;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * avgw;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = 2 * K * G;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the best so far. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2 * K * G > best_n) emit();
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    /* Header "n m" from graph_to_text (ignored), then the flat group stream. */
    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) {
        printf("0 0\n");
        return 0;
    }
    int ng_read = 0;
    if (scanf("%d", &ng_read) != 1) ng_read = 0;
    int cnt_g = 0;
    for (int i = 0; i < ng_read && cnt_g < MAXNG; i++) {
        int Gi = 0;
        if (scanf("%d", &Gi) != 1 || Gi < 1 || Gi > 4000) break;
        int *tab = malloc(sizeof(int) * (size_t)Gi * (size_t)Gi);
        int bad = 0, fail = 0;
        for (long x = 0; x < (long)Gi * (long)Gi; x++) {
            int v = 0;
            if (scanf("%d", &v) != 1) { fail = 1; break; }
            tab[x] = v;
            if (v < 0 || v >= Gi) bad = 1;
        }
        if (fail) { free(tab); break; }
        if (bad || tab[0] != 0) { free(tab); continue; }
        gord[cnt_g] = Gi;
        gtab[cnt_g] = tab;
        cnt_g++;
    }
    ng = cnt_g;
    if (ng == 0) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < ng; i++)
        if (gord[i] > maxG) maxG = gord[i];

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    alloc_all();

    while (elapsed() < DEADLINE) {
        /* Pick a group and a base size K such that 2*K*G beats the best so far. */
        int gi = -1, k = 1;
        int off = rnd_int(ng);
        for (int j = 0; j < ng && gi < 0; j++) {
            int cand = (off + j) % ng;
            int feas[MAXK], nf = 0;
            for (int kk = 1; kk <= MAXK; kk++)
                if (2LL * kk * gord[cand] > (long long)best_n) feas[nf++] = kk;
            if (nf == 0) continue;
            gi = cand;
            k = feas[rnd_int(nf)];
        }
        if (gi < 0) break;

        K = k;
        G = gord[gi];
        MUL = gtab[gi];
        N = 2 * K * G;
        T = DEG * K;
        for (int b = 0; b < 2 * K; b++) wt[b] = 1;
        sumw = 2 * K;
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    (void)hn;
    (void)hm;
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: finite groups given as multiplication tables.
# Identity is always index 0.
# ----------------------------------------------------------------------------

_GF_CACHE = {}


def _gf(q):
    """Cached GF(q) object (numpy tables stay small enough to keep)."""
    if q not in _GF_CACHE:
        _GF_CACHE[q] = lib.GF(q)
    return _GF_CACHE[q]


def _affine_group(q, h):
    """Affine group F_q x| H, H the subgroup of order h in F_q^*. Element (a, b) is coded a*h + j with b = H[j]."""
    if h < 1 or (q - 1) % h:
        return None
    F = _gf(q)
    add = F.add_table.tolist()
    mul = F.mul_table.tolist()
    gen = F.pow(F.primitive_element(), (q - 1) // h)
    H = [F.pow(gen, k) for k in range(h)]
    hidx = {x: j for j, x in enumerate(H)}
    hm = [[hidx[mul[H[i]][H[j]]] for j in range(h)] for i in range(h)]
    G = q * h
    pa = [x // h for x in range(G)]
    pj = [x % h for x in range(G)]
    tab = [0] * (G * G)
    for x in range(G):
        a1, j1 = pa[x], pj[x]
        row_mul = mul[H[j1]]
        row_add = add[a1]
        hrow = hm[j1]
        base = x * G
        for y in range(G):
            # (a1, b1) * (a2, b2) = (a1 + b1 a2, b1 b2)
            tab[base + y] = row_add[row_mul[pa[y]]] * h + hrow[pj[y]]
    return G, tab


def _dihedral(m):
    """Dihedral group of order 2m; element (i, e) coded e*m + i."""
    G = 2 * m
    tab = [0] * (G * G)
    for x in range(G):
        e1, i1 = divmod(x, m)
        for y in range(G):
            e2, i2 = divmod(y, m)
            i = (i1 + i2) % m if e1 == 0 else (i1 - i2) % m
            tab[x * G + y] = ((e1 + e2) & 1) * m + i
    return G, tab


def _cyclic(c):
    tab = [0] * (c * c)
    for x in range(c):
        for y in range(c):
            tab[x * c + y] = (x + y) % c
    return c, tab


def _direct(A, B):
    GA, ta = A
    GB, tb = B
    G = GA * GB
    tab = [0] * (G * G)
    pa = [x // GB for x in range(G)]
    pb = [x % GB for x in range(G)]
    for x in range(G):
        ra = pa[x] * GA
        rb = pb[x] * GB
        base = x * G
        for y in range(G):
            tab[base + y] = ta[ra + pa[y]] * GB + tb[rb + pb[y]]
    return G, tab


def _spec_order(s):
    kind = s[0]
    if kind == 'aff':
        return s[1] * s[2]
    if kind == 'dih':
        return 2 * s[1]
    if kind == 'cyc':
        return s[1]
    return _spec_order(s[1]) * s[2]  # 'dir'


def _spec_build(s):
    kind = s[0]
    if kind == 'aff':
        return _affine_group(s[1], s[2])
    if kind == 'dih':
        return _dihedral(s[1])
    if kind == 'cyc':
        return _cyclic(s[1])
    return _direct(_spec_build(s[1]), _cyclic(s[2]))


def _group_specs(lo, hi):
    specs = []
    for q in range(3, hi + 1):
        if not lib.is_prime_power(q):
            continue
        for h in range(1, q):
            if (q - 1) % h == 0 and lo <= q * h <= hi:
                specs.append(('aff', q, h))
    for m in range(3, hi // 2 + 1):
        if lo <= 2 * m <= hi:
            specs.append(('dih', m))
    for m in range(lo, hi + 1):
        specs.append(('cyc', m))
    for s in list(specs):
        if s[0] == 'cyc':
            continue
        for c in (2, 3):
            if lo <= _spec_order(s) * c <= hi:
                specs.append(('dir', s, c))
    return specs


ENTRY_CAP = 1_200_000  # total table entries passed to C (keeps stdin size sane)


def _build_groups(lo, hi, seed, deadline):
    """Build a shuffled, budget-limited list of (G, table) pairs with lo <= G <= hi."""
    specs = _group_specs(lo, hi)
    random.Random(seed).shuffle(specs)
    groups = []
    entries = 0
    for s in specs:
        if time.monotonic() > deadline or len(groups) >= 40:
            break
        G = _spec_order(s)
        if entries + G * G > ENTRY_CAP:
            continue
        try:
            res = _spec_build(s)
        except Exception:
            continue
        if res is None:
            continue
        Gb, tab = res
        if Gb != G or len(tab) != G * G or tab[0] != 0:
            continue
        groups.append((G, tab))
        entries += G * G
    return groups


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Driver: baselines, then the group-table annealer. Any failure keeps the
# best valid graph found so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Group orders G with n = 2*K*G (K in 1..4) in a window around the
    # target density: G <= moore/2 since K >= 1.
    lo = max(2, (45 * moore // 100) // 8)
    hi = min(moore // 2, 781)
    if lo <= hi:
        group_deadline = start + 0.2 * time_limit
        try:
            groups = _build_groups(lo, hi, seed, group_deadline)
        except Exception:
            groups = []

        if groups:
            try:
                flat = [len(groups)]
                for G, tab in groups:
                    flat.append(G)
                    flat.extend(tab)
                if len(flat) % 2:
                    flat.append(0)
                edges = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
                remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
                if remaining >= 2.0:
                    out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                                    stdin_graph=(1, edges), timeout=remaining + 10.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

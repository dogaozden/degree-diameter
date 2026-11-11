"""Bi-Cayley search over arbitrary finite groups, with conjugacy-reduced exhaustive checks.

New in this version:
  * The C engine accepts any finite group given by permutation generators. It computes the
    closure, then builds the multiplication table from a BFS tree and per-generator
    right-multiplication maps. Metacyclic groups are still built directly by formula.
  * Non-metacyclic families come from Python: PGL(2,q) and PSL(2,q), SL(2,7), GL(2,3) and
    AGL(2,3), the hyperoctahedral group B_4, Frobenius-type groups GF(q) x| Z_s for
    q = p^k with k >= 2, and direct products of small groups with cyclic groups.
  * For a bi-Cayley graph with S = {0, a, s_2, ..., s_{d-1}}, conjugation by g maps S to
    g S g^-1 and gives an isomorphic graph. So a runs over conjugacy-class representatives
    only. For d = 3 the search over one group is then complete and cheap.
  * Orders are scanned upward from about 0.49 * Moore/2 over all candidate groups of each
    order, and the largest success is kept.
Every graph found is re-verified by a full BFS in C and by lib.is_valid in Python.
If nothing is found, the program returns the valid start graph.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define MAXV (2 * MAXN)
#define MAXDEG 16
#define MAXK 256
#define MAXGEN 8
#define MAXEXTRA 512
#define MAXGRP 8192
#define HSIZE 8192
#define CAP_NONAB 200000LL
#define CAP_AB 3000LL

static int d, D;
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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ---------------- current group: multiplication table MT (stride NN), inverses INV */
static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NN;

static void compute_inverses(void) {
    int n = NN;
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------- metacyclic groups Z_m x| Z_k, element (a,b) coded a*k+b */
typedef struct { int m, k, r, ab; } Grp;
static Grp grps[MAXGRP];
static int ngrps;

static void add_grp(int m, int k, int r) {
    if (ngrps >= MAXGRP) return;
    grps[ngrps].m = m;
    grps[ngrps].k = k;
    grps[ngrps].r = r;
    grps[ngrps].ab = (m == 1 || r == 1);
    ngrps++;
}

/* Nonabelian groups first (pass 0), then abelian ones (pass 1). */
static void enum_meta(int n) {
    ngrps = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1) add_grp(1, k, 0);
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                add_grp(m, k, r);
            }
        }
    }
}

static void build_meta(const Grp *G) {
    int n = G->m * G->k;
    NN = n;
    static int rp[MAXN];
    rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) rp[b] = (int)((long)rp[b - 1] * G->r % G->m);
    for (int x = 0; x < n; x++) {
        int a = x / G->k, b = x % G->k;
        for (int y = 0; y < n; y++) {
            int c = y / G->k, e = y % G->k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G->m) * G->k + (b + e) % G->k;
        }
    }
    compute_inverses();
}

/* ---------------- generic permutation groups (closure in C) */
typedef struct { int K, ng, order; unsigned char g[MAXGEN][MAXK]; } PG;
static PG extras[MAXEXTRA];
static int nextra = 0;

static unsigned char EP[MAXN][MAXK];
static int ne;
static int htab[HSIZE];
static int par_[MAXN], pg_[MAXN];
static int R[MAXGEN][MAXN];

static uint32_t phash(const unsigned char *p, int K) {
    uint32_t h = 2166136261u;
    for (int i = 0; i < K; i++) { h ^= p[i]; h *= 16777619u; }
    return h;
}

static int hfind(const unsigned char *p, int K) {
    uint32_t h = phash(p, K) & (HSIZE - 1);
    while (htab[h]) {
        int idx = htab[h] - 1;
        if (memcmp(EP[idx], p, (size_t)K) == 0) return idx;
        h = (h + 1) & (HSIZE - 1);
    }
    return -1;
}

static void hinsert(int idx, int K) {
    uint32_t h = phash(EP[idx], K) & (HSIZE - 1);
    while (htab[h]) h = (h + 1) & (HSIZE - 1);
    htab[h] = idx + 1;
}

/* c = apply a first, then b. */
static void compose(const unsigned char *a, const unsigned char *b, unsigned char *c, int K) {
    for (int i = 0; i < K; i++) c[i] = b[a[i]];
}

/* Closure of the generators; returns the order, or -1 if it exceeds cap. Fills EP, par_, pg_. */
static int closure(const PG *G, int cap) {
    int K = G->K;
    memset(htab, 0, sizeof(htab));
    for (int i = 0; i < K; i++) EP[0][i] = (unsigned char)i;
    hinsert(0, K);
    ne = 1;
    par_[0] = -1;
    pg_[0] = -1;
    for (int e = 0; e < ne; e++) {
        for (int g = 0; g < G->ng; g++) {
            unsigned char tmp[MAXK];
            compose(EP[e], G->g[g], tmp, K);
            if (hfind(tmp, K) < 0) {
                if (ne >= cap) return -1;
                memcpy(EP[ne], tmp, (size_t)K);
                hinsert(ne, K);
                par_[ne] = e;
                pg_[ne] = g;
                ne++;
            }
        }
    }
    return ne;
}

/* Table from the last closure: column y = column par(y) followed by the generator. */
static void table_from_closure(const PG *G) {
    int N = ne, K = G->K;
    NN = N;
    for (int g = 0; g < G->ng; g++)
        for (int z = 0; z < N; z++) {
            unsigned char tmp[MAXK];
            compose(EP[z], G->g[g], tmp, K);
            int idx = hfind(tmp, K);
            R[g][z] = idx < 0 ? 0 : idx;
        }
    for (int x = 0; x < N; x++) MT[x * N] = x;
    for (int y = 1; y < N; y++) {
        int p = par_[y], g = pg_[y];
        for (int x = 0; x < N; x++) MT[x * N + y] = R[g][MT[x * N + p]];
    }
    compute_inverses();
}

/* ---------------- bi-Cayley check */
static int dist_[MAXV], queue_[MAXV];

/* 1 iff every vertex of the bi-Cayley graph is within D of src.
 * A_x = x, B_h = NN + h. A_x ~ B_{x s}, B_h ~ A_{h s^-1}. */
static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            const int *row = MT + (size_t)v * n;
            for (int i = 0; i < d; i++) {
                int u = n + row[S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            const int *row = MT + (size_t)(v - n) * n;
            for (int i = 0; i < d; i++) {
                int u = row[INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

static int try_set(const int *S) {
    return reach_all(S, 0) && reach_all(S, NN);
}

/* Conjugacy class representatives of the non-identity elements. */
static int reps[MAXN], nreps;
static void conj_reps(void) {
    static unsigned char seen[MAXN];
    int n = NN;
    memset(seen, 0, sizeof(seen));
    nreps = 0;
    for (int x = 1; x < n; x++) {
        if (seen[x]) continue;
        reps[nreps++] = x;
        for (int g = 0; g < n; g++) {
            int y = MT[MT[g * n + x] * n + INV[g]];
            seen[y] = 1;
        }
    }
}

static int curS[MAXDEG];

static int comb_next(int *c, int r, int m) {
    int i = r - 1;
    while (i >= 0 && c[i] == m - r + i) i--;
    if (i < 0) return 0;
    c[i]++;
    for (int j = i + 1; j < r; j++) c[j] = c[j - 1] + 1;
    return 1;
}

static long long nchecks = 0;

/* Search S = {0, a, others} with a a class representative. Exhaustive when small, else random.
 * Returns 1 and sets curS on success. */
static int search_table(long long cap) {
    conj_reps();
    int r = d - 2, m = NN - 2;
    if (nreps == 0 || m < r) return 0;
    double total = (double)nreps;
    for (int i = 0; i < r; i++) total = total * (m - i) / (i + 1);
    int S[MAXDEG], L[MAXN], c[MAXDEG];
    if (total <= (double)cap) {
        for (int ai = 0; ai < nreps; ai++) {
            int a = reps[ai], nl = 0;
            for (int x = 1; x < NN; x++) if (x != a) L[nl++] = x;
            S[0] = 0;
            S[1] = a;
            for (int j = 0; j < r; j++) c[j] = j;
            do {
                for (int j = 0; j < r; j++) S[2 + j] = L[c[j]];
                if ((++nchecks & 63) == 0 && now() >= t_end) return 0;
                if (try_set(S)) {
                    memcpy(curS, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            } while (comb_next(c, r, nl));
        }
        return 0;
    }
    for (long long it = 0; it < cap; it++) {
        if ((++nchecks & 63) == 0 && now() >= t_end) return 0;
        int a = reps[rndint(nreps)];
        S[0] = 0;
        S[1] = a;
        for (int j = 0; j < r; j++) {
            for (;;) {
                int x = 1 + rndint(NN - 1);
                int dup = (x == a);
                for (int t = 0; t < 2 + j && !dup; t++) if (S[t] == x) dup = 1;
                if (!dup) { S[2 + j] = x; break; }
            }
        }
        if (try_set(S)) {
            memcpy(curS, S, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

/* ---------------- explicit graph verification and recording */
static int adjl[MAXV][MAXDEG], degl[MAXV];

static void add_e(int u, int v) {
    adjl[u][degl[u]++] = v;
    adjl[v][degl[v]++] = u;
}

static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++) if (degl[v] > d || degl[v] < 1) return 0;
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static int bestN = 0, bestM = 0;
static int best_u[MAXN * MAXDEG], best_v[MAXN * MAXDEG];

static int record_success(void) {
    int n = NN, V = 2 * n;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++) add_e(x, n + MT[x * n + curS[i]]);
    if (!verify_explicit(V)) return 0;
    if (n <= bestN) return 1;
    int m = 0;
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) { best_u[m] = u; best_v[m] = adjl[u][i]; m++; }
    bestM = m;
    bestN = n;
    return 1;
}

/* ---------------- main */
int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed budget nlo nhi\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]), nhi = atoi(argv[6]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + budget;

    /* stdin: header "0 m", then groups as [ng, K, ng*K perm entries], terminated by ng = 0 */
    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) hm = 0;
    (void)hn;
    (void)hm;
    nextra = 0;
    for (;;) {
        int ng = 0, K = 0;
        if (scanf("%d", &ng) != 1) break;
        if (ng == 0) break;
        if (scanf("%d", &K) != 1) break;
        int bad = (ng < 0 || ng > MAXGEN || K < 1 || K > MAXK);
        int ok = !bad, eof = 0;
        PG tmp;
        memset(&tmp, 0, sizeof(tmp));
        tmp.ng = ng;
        tmp.K = K;
        for (int g = 0; g < ng && !eof; g++) {
            unsigned char seen[MAXK];
            memset(seen, 0, sizeof(seen));
            for (int i = 0; i < K; i++) {
                int v = 0;
                if (scanf("%d", &v) != 1) { eof = 1; break; }
                if (!ok) continue;
                if (v < 0 || v >= K || seen[v]) { ok = 0; continue; }
                seen[v] = 1;
                tmp.g[g][i] = (unsigned char)v;
            }
        }
        if (eof) break;
        if (!ok) continue;
        if (nextra < MAXEXTRA) {
            int ord = closure(&tmp, MAXN);
            if (ord >= nlo && ord <= nhi) {
                tmp.order = ord;
                extras[nextra++] = tmp;
            }
        }
    }

    if (d >= 2 && d <= MAXDEG && D >= 2) {
        for (int N = nlo; N <= nhi && now() < t_end; N++) {
            int done = 0;
            /* generic permutation groups of this order first (non-metacyclic families) */
            for (int e = 0; e < nextra && !done && now() < t_end; e++) {
                if (extras[e].order != N) continue;
                if (closure(&extras[e], MAXN) != N) continue;
                table_from_closure(&extras[e]);
                if (search_table(CAP_NONAB) && record_success()) done = 1;
            }
            /* metacyclic groups: nonabelian first, abelian last */
            enum_meta(N);
            for (int gi = 0; gi < ngrps && !done && now() < t_end; gi++) {
                const Grp *G = &grps[gi];
                build_meta(G);
                if (search_table(G->ab ? CAP_AB : CAP_NONAB) && record_success()) done = 1;
            }
        }
    }

    if (bestN > 0) {
        printf("%d %d\n", 2 * bestN, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", best_u[i], best_v[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


# ---------------------------------------------------------------- permutation families

def _cycle_gens(k):
    """Generator list of the cyclic group Z_k acting on k points."""
    return [[(i + 1) % k for i in range(k)]]


def _direct(G1, d1, G2, d2):
    """Generators of G1 x G2 acting on the disjoint union of d1 and d2 points."""
    out = [g + [d1 + i for i in range(d2)] for g in G1]
    out += [list(range(d1)) + [d1 + h[i] for i in range(d2)] for h in G2]
    return out


def _pgl2(q, psl=False):
    """Generators of PGL(2,q) (or PSL(2,q) for odd q when psl) on the projective line; infinity = q."""
    F = lib.GF(q)
    g = F.primitive_element()
    a = F.mul(g, g) if psl else g
    inf = q
    T = [F.add(x, 1) for x in range(q)] + [inf]
    M = [F.mul(a, x) for x in range(q)] + [inf]
    J = [inf if x == 0 else F.neg(F.inv(x)) for x in range(q)] + [0]
    return [T, M, J]


def _affine(p, mats):
    """Permutations of the p*p vectors (index x*p+y) for the affine maps v -> M v + t."""
    gens = []
    for M, t in mats:
        perm = []
        for x in range(p):
            for y in range(p):
                X = (M[0][0] * x + M[0][1] * y + t[0]) % p
                Y = (M[1][0] * x + M[1][1] * y + t[1]) % p
                perm.append(X * p + Y)
        gens.append(perm)
    return gens


def _frobenius(F, s):
    """GF(q) x| <alpha> with alpha of order s (x -> alpha x + b): non-metacyclic when q = p^k, k >= 2."""
    w = F.primitive_element()
    gens = [[F.add(x, F.pow(w, i)) for x in range(F.q)] for i in range(F.k)]
    alpha = F.pow(w, (F.q - 1) // s)
    gens.append([F.mul(alpha, x) for x in range(F.q)])
    return gens


def _b4():
    """Hyperoctahedral group B_4 (order 384) on 8 points: i = +e_i, 4+i = -e_i."""
    s0 = list(range(8))
    s0[0], s0[4] = 4, 0
    t01 = list(range(8))
    t01[0], t01[1] = 1, 0
    t01[4], t01[5] = 5, 4
    c4 = [(i + 1) % 4 for i in range(4)] + [4 + (i + 1) % 4 for i in range(4)]
    return [s0, t01, c4]


_S4 = [[1, 0, 2, 3], [1, 2, 3, 0]]
_A4 = [[1, 2, 0, 3], [1, 0, 3, 2]]
_GL23 = _affine(3, [([[1, 1], [0, 1]], (0, 0)),
                    ([[0, 1], [2, 0]], (0, 0)),
                    ([[2, 0], [0, 1]], (0, 0))])
_AGL23 = _GL23 + _affine(3, [([[1, 0], [0, 1]], (1, 0)),
                             ([[1, 0], [0, 1]], (0, 1))])
_SL27 = _affine(7, [([[1, 1], [0, 1]], (0, 0)),
                    ([[1, 0], [1, 1]], (0, 0))])


def candidate_groups(lo, hi):
    """Permutation generator lists of candidate groups, with orders possibly in [lo, hi]."""
    out = []
    small = {
        "S4": (_S4, 4, 24),
        "A4": (_A4, 4, 12),
        "GL23": (_GL23, 9, 48),
        "S5": (_pgl2(5), 6, 120),
        "A5": (_pgl2(5, True), 6, 60),
        "PSL27": (_pgl2(7, True), 8, 168),
    }
    for gens, deg, order in small.values():
        for k in range(2, hi // order + 1):
            if lo <= order * k <= hi:
                out.append(_direct(gens, deg, _cycle_gens(k), k))
    out += [_GL23, _AGL23, _SL27, _pgl2(7), _pgl2(9, True), _pgl2(8), _b4()]
    for q in (25, 27, 49, 64, 81, 121, 125, 169, 243):
        F = lib.GF(q)
        for s in range(2, q):
            if (q - 1) % s == 0 and lo <= q * s <= hi:
                out.append(_frobenius(F, s))
    return out


def _pack(groups):
    """Flatten groups into (u, v) pairs for the C reader: [ng, K, perms...] ..., terminated by 0."""
    flat = []
    for gens in groups:
        if not gens:
            continue
        K = len(gens[0])
        if not (1 <= len(gens) <= 8 and 1 <= K <= 256):
            continue
        flat += [len(gens), K]
        for g in gens:
            flat += list(g)
    flat += [0]
    if len(flat) % 2:
        flat.append(0)
    return [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    nhi = min(moore // 2, 511)
    nlo = max(d + 1, best[0] // 2 + 1, int(0.49 * moore) // 2)
    if nlo > nhi:
        return best

    try:
        edges = _pack(candidate_groups(nlo, nhi))
    except Exception:
        edges = _pack([])

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo, nhi],
                         stdin_graph=(0, edges), timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best

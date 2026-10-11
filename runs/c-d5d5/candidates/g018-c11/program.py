"""Bold change: permutation-group bi-Cayley search for the weakest case (d=5, D=5).

Python lists permutation groups (PGL(2,7), PSL(2,7), S5 x Z2, A5 x Z3, S4 x Z_k, ...)
and metacyclic affine groups Z_m x| <r>, with orders between 60 and 341. It passes them
to C as a compact spec string. C builds each group's full multiplication table from
its permutations. It then searches bipartite lifts over the group with a base of
kb = 1..3 vertices per side, d darts per base vertex, and voltages in the group.
Left multiplication is an automorphism, so the diameter test needs only 2kb BFS runs.
Annealing runs over voltages and layer permutations. Any group whose lift order
2*kb*|G| beats the current best can win. The result is validated in Python and
compared with K_{d,d} and the known D=3 constructions, so every case returns a valid graph.
"""
import math
import random
import time

import lib

C_SOURCE = r'''
/* Permutation-group bi-lift search.
 *
 * Usage:  prog d D seed time_limit spec
 * spec:   tokens. "A m r N" = affine group Z_m x| <r> on m points (order N).
 *         "P deg ng N g1... " = explicit generators (ng permutations of deg points).
 * stdout: "n m" then m lines "u v" of the best bipartite graph found.
 *
 * A lift over group G with base kb: A_{i,x} ~ B_{j,x*s} for each dart (i,j,s).
 * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS of depth D
 * from A_{i,e} (i<kb) and B_{j,e} (j<kb) reaches all 2kb|G| vertices.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define GCAP 512
#define MAXP 400
#define MAXGEN 3
#define MAXGR 1024
#define MAXKB 3
#define MAXD 16
#define MAXDART (MAXD * MAXKB)
#define MAXV (2 * MAXKB * GCAP)
#define MAXE (MAXDART * GCAP)
#define HSZ 4096
#define BIGCOST 1000000000L

typedef struct {
    int type, m, r;              /* type 0: affine Z_m x| <r> */
    int deg, ng, N;              /* type 1: explicit permutations; N is the planned order */
    unsigned short gp[MAXGEN][MAXP];
    int built, bad, nb;
    unsigned short *T;           /* T[x*nb+y] = x*y */
    int *INV;
} Grp;

static Grp GR[MAXGR];
static int NGR = 0;
static unsigned short EP[GCAP][MAXP];
static int NE;
static int HT[HSZ];

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
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

/* ------------------------------------------------------------ spec parsing */

static long rdint(const char **p) {
    while (**p == ' ' || **p == '\t' || **p == '\n') (*p)++;
    char *e;
    long v = strtol(*p, &e, 10);
    *p = e;
    return v;
}

static void parse_spec(const char *s) {
    const char *p = s;
    for (;;) {
        while (*p == ' ' || *p == '\t' || *p == '\n') p++;
        if (!*p || NGR >= MAXGR) break;
        char c = *p++;
        Grp *g = &GR[NGR];
        memset(g, 0, sizeof *g);
        if (c == 'A') {
            g->type = 0;
            g->m = (int)rdint(&p);
            g->r = (int)rdint(&p);
            g->N = (int)rdint(&p);
            if (g->m < 1 || g->m > MAXP) break;
        } else if (c == 'P') {
            g->type = 1;
            g->deg = (int)rdint(&p);
            g->ng = (int)rdint(&p);
            g->N = (int)rdint(&p);
            if (g->deg < 1 || g->deg > MAXP || g->ng < 1 || g->ng > MAXGEN) break;
            for (int i = 0; i < g->ng; i++)
                for (int k = 0; k < g->deg; k++)
                    g->gp[i][k] = (unsigned short)rdint(&p);
        } else {
            break;
        }
        NGR++;
    }
}

/* ------------------------------------------------------------ groups */

static uint32_t hperm(const unsigned short *p, int P) {
    uint32_t h = 2166136261u;
    for (int k = 0; k < P; k++) { h ^= p[k]; h *= 16777619u; }
    return h;
}

/* Index of p among EP[0..NE), or -1; if absent and slot != NULL, *slot is the free hash slot. */
static int lookup(const unsigned short *p, int P, uint32_t *slot) {
    uint32_t h = hperm(p, P) & (HSZ - 1);
    while (HT[h] >= 0) {
        if (memcmp(EP[HT[h]], p, sizeof(unsigned short) * P) == 0) return HT[h];
        h = (h + 1) & (HSZ - 1);
    }
    if (slot) *slot = h;
    return -1;
}

static int build_group(Grp *g) {
    if (g->built) return !g->bad;
    g->built = 1;
    int P = g->type == 0 ? g->m : g->deg;
    unsigned short gen[MAXGEN][MAXP];
    int ng;
    if (g->type == 0) {
        ng = 2;
        for (int x = 0; x < g->m; x++) {
            gen[0][x] = (unsigned short)((x + 1) % g->m);
            gen[1][x] = (unsigned short)(((long)g->r * x) % g->m);
        }
    } else {
        ng = g->ng;
        memcpy(gen, g->gp, sizeof gen);
    }
    for (int i = 0; i < HSZ; i++) HT[i] = -1;
    for (int k = 0; k < P; k++) EP[0][k] = (unsigned short)k;
    {
        uint32_t slot;
        lookup(EP[0], P, &slot);
        HT[slot] = 0;
    }
    NE = 1;
    unsigned short c[MAXP];
    for (int e = 0; e < NE; e++)
        for (int gi = 0; gi < ng; gi++) {
            for (int k = 0; k < P; k++) c[k] = gen[gi][EP[e][k]];
            uint32_t slot;
            if (lookup(c, P, &slot) < 0) {
                if (NE >= GCAP) { g->bad = 1; return 0; }
                memcpy(EP[NE], c, sizeof(unsigned short) * P);
                HT[slot] = NE++;
            }
        }
    int N = NE;
    g->nb = N;
    g->T = malloc(sizeof(unsigned short) * (size_t)N * N);
    g->INV = malloc(sizeof(int) * (size_t)N);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            for (int k = 0; k < P; k++) c[k] = EP[x][EP[y][k]];
            int z = lookup(c, P, NULL);
            if (z < 0) { g->bad = 1; return 0; }
            g->T[x * N + y] = (unsigned short)z;
        }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (g->T[x * N + y] == 0) g->INV[x] = y;
    return 1;
}

/* ------------------------------------------------------------ lifts */

static int KB, ND, N;
static const unsigned short *TT;
static const int *INVT;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int INV_J[MAXKB][MAXD];
static int VIS[MAXV], VST = 0, QU[MAXV];
static int OU[MAXE], OV[MAXE], NOUT;

static int has_dup(void) {
    for (int a = 0; a < ND; a++)
        for (int b = a + 1; b < ND; b++)
            if (DI[a] == DI[b] && DJ[a] == DJ[b] && DS[a] == DS[b]) return 1;
    return 0;
}

/* Unreached (source, vertex) pairs over the 2KB orbit representatives. */
static long lift_cost(void) {
    if (has_dup()) return BIGCOST;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) INV_J[DJ[l * KB + i]][l] = i;
    int total = 2 * KB * N;
    long cost = 0;
    for (int s = 0; s < 2 * KB; s++) {
        int src = s * N;
        VST++;
        int head = 0, tail = 0;
        VIS[src] = VST;
        QU[tail++] = src;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = QU[head++];
                int blk = u / N, x = u % N;
                if (blk < KB) {
                    for (int l = 0; l < d; l++) {
                        int t = l * KB + blk;
                        int v = (KB + DJ[t]) * N + TT[x * N + DS[t]];
                        if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                    }
                } else {
                    int j = blk - KB;
                    for (int l = 0; l < d; l++) {
                        int i = INV_J[j][l];
                        int t = l * KB + i;
                        int v = i * N + TT[x * N + INVT[DS[t]]];
                        if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                    }
                }
            }
        }
        cost += total - tail;
    }
    return cost;
}

static void emit(void) {
    NOUT = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++) {
            OU[NOUT] = DI[t] * N + x;
            OV[NOUT] = (KB + DJ[t]) * N + TT[x * N + DS[t]];
            NOUT++;
        }
}

/* One annealing run over voltages and layer permutations. On success the lift is in OU/OV. */
static int lift_run(long steps) {
    for (int l = 0; l < d; l++) {
        int perm[MAXKB];
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < KB; i++) {
            int t = l * KB + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(N);
        }
    }
    long cost = lift_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double Tm = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (KB < 2 || rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(N);
            if (nv == old) continue;
            DS[t] = nv;
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) cost = c2;
            else DS[t] = old;
        } else {
            int l = rndint(d);
            int i1 = rndint(KB), i2 = rndint(KB);
            if (i1 == i2) continue;
            int t1 = l * KB + i1, t2 = l * KB + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    if (cost != 0) return 0;
    emit();
    return 1;
}

/* ------------------------------------------------------------ main */

static int BU[MAXE], BV[MAXE], BN;
static int best_n;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [spec]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit * 0.97;
    if (argc > 5) parse_spec(argv[5]);

    if (d < 1 || d > MAXD || D < 2) { printf("2 1\n0 1\n"); return 0; }

    best_n = 2 * d;
    BN = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) { BU[BN] = a; BV[BN] = d + b; BN++; }

    long moore = moore_bound();
    long fails = 0;
    while (now() < t_end && best_n < moore && NGR > 0) {
        int kb = 1 + rndint(3);
        int cand[64], nc = 0;
        for (int tries = 0; tries < 80 && nc < 64; tries++) {
            int k = rndint(NGR);
            Grp *g = &GR[k];
            if (g->bad) continue;
            long tot = 2L * kb * g->N;
            if (tot <= best_n || tot > moore) continue;
            cand[nc++] = k;
        }
        if (nc == 0) { fails++; continue; }
        int gi = cand[rndint(nc)];
        if (rndint(2) == 0)
            for (int c = 0; c < nc; c++)
                if (GR[cand[c]].N < GR[gi].N) gi = cand[c];
        if (!build_group(&GR[gi])) continue;

        KB = kb;
        N = GR[gi].nb;
        TT = GR[gi].T;
        INVT = GR[gi].INV;
        ND = d * KB;
        long tot = 2L * KB * N;
        if (tot <= best_n || tot > moore) { fails++; continue; }

        long extra = (fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        if (lift_run(steps)) {
            best_n = (int)tot;
            BN = NOUT;
            memcpy(BU, OU, sizeof(int) * NOUT);
            memcpy(BV, OV, sizeof(int) * NOUT);
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", best_n, BN);
    for (int i = 0; i < BN; i++) printf("%d %d\n", BU[i], BV[i]);
    return 0;
}
'''


# ------------------------------------------------------------ Python side

def _cycle(n, cyc):
    p = list(range(n))
    for i, x in enumerate(cyc):
        p[x] = cyc[(i + 1) % len(cyc)]
    return tuple(p)


def _order(gens, deg, cap=400):
    """Order of the permutation group generated by gens, or None if above cap."""
    idt = tuple(range(deg))
    seen = {idt}
    frontier = [idt]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[k] for k in x)
                if y not in seen:
                    seen.add(y)
                    if len(seen) > cap:
                        return None
                    nxt.append(y)
        frontier = nxt
    return len(seen)


def _S(n):
    return n, [_cycle(n, [0, 1]), _cycle(n, list(range(n)))]


def _A5():
    return 5, [_cycle(5, [0, 1, 2]), _cycle(5, [0, 1, 2, 3, 4])]


def _A4():
    return 4, [_cycle(4, [0, 1, 2]), _cycle(4, [1, 2, 3])]


def _Z(n):
    return n, [_cycle(n, list(range(n)))]


def _prod(a, b):
    da, ga = a
    db, gb = b
    gens = [tuple(g) + tuple(range(da, da + db)) for g in ga]
    gens += [tuple(range(da)) + tuple(da + x for x in h) for h in gb]
    return da + db, gens


def _psl27():
    """PSL(2,7) on the projective line 0..6, infinity = 7."""
    inv_neg = lambda x: 7 if x == 0 else (-pow(x, 5, 7)) % 7   # -1/x, since x^5 = x^-1
    f1 = tuple([(x + 1) % 7 for x in range(7)] + [7])
    f2 = tuple([(2 * x) % 7 for x in range(7)] + [7])
    f3 = tuple([inv_neg(x) for x in range(7)] + [0])
    return 8, [f1, f2, f3]


def _pgl27():
    inv_neg = lambda x: 7 if x == 0 else (-pow(x, 5, 7)) % 7
    f1 = tuple([(x + 1) % 7 for x in range(7)] + [7])
    f2 = tuple([(3 * x) % 7 for x in range(7)] + [7])
    f3 = tuple([inv_neg(x) for x in range(7)] + [0])
    return 8, [f1, f2, f3]


_SPEC = None


def _group_spec():
    """Compact spec string for the C engine: permutation groups plus affine groups."""
    global _SPEC
    if _SPEC is not None:
        return _SPEC
    S5, A5, S4, A4, S3 = _S(5), _A5(), _S(4), _A4(), _S(3)
    Z2, Z3 = _Z(2), _Z(3)
    fams = [_pgl27(), _psl27(), _prod(_psl27(), Z2), _prod(S5, Z2), _prod(A5, Z3),
            _prod(S4, _Z(7)), _prod(S4, _Z(8)), _prod(S4, _Z(9)), _prod(S4, A4),
            _prod(A4, A4), _prod(S4, S3), _prod(_prod(S4, S3), Z2), S5, A5, S4,
            _prod(A5, Z2), _prod(_prod(A5, Z2), Z2), _prod(S4, Z2), _prod(_prod(S4, Z2), Z2)]
    for a, b in [(12, 15), (10, 17), (13, 14), (11, 16), (18, 10), (20, 9), (12, 12)]:
        fams.append(_prod(_Z(a), _Z(b)))
    parts = []
    for deg, gens in fams:
        N = _order(gens, deg)
        if N and 60 <= N <= 341:
            parts.append(f"P {deg} {len(gens)} {N} " + " ".join(str(x) for g in gens for x in g))
    aff = []
    for m in range(2, 342):
        for r in range(1, m):
            if math.gcd(r, m) != 1:
                continue
            x, k = r % m, 1
            while x != 1 and m * (k + 1) <= 341:
                x = x * r % m
                k += 1
            if x == 1 and 60 <= m * k <= 341:
                aff.append(f"A {m} {r} {m * k}")
    rng = random.Random(20240601)
    if len(aff) > 160:
        aff = rng.sample(aff, 160)
    _SPEC = " ".join(parts + aff)
    return _SPEC


def _known_start(d, D):
    """Known constructions Python builds directly (only D = 3 here)."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)     # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2, safe fallback
    try:
        start = _known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D) or d > 16:
        return best

    budget = 0.92 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), _group_spec()],
                         stdin_graph=None, timeout=budget + 3.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best

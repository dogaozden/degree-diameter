"""Program: multi-orbit bi-Cayley (voltage) lifts over metacyclic and PSL/SL(2,q) groups.

New idea in this version: P-orbit lifts with coupled permutation darts.
  * Base graph: P "A" orbits and P "B" orbits, each a copy of a group G of order N.
    For each dart index k < d, a permutation pi_k of {0..P-1} and a voltage g_{i,k} in G
    join A_i x to B_{pi_k(i)} (x*g_{i,k}). Every A and B vertex then has degree d.
    Order = 2*P*N. P = 1 is the classic bi-Cayley graph, so the old search is a special case.
  * Left multiplication by any h in G is an automorphism that fixes each orbit, so validity
    needs BFS only from the 2P roots A_i e and B_i e. Each BFS must reach all 2PN vertices
    within D steps.
  * Simple-graph condition: for each A_i, the pairs (pi_k(i), g_{i,k}) must be distinct.
    Violations are penalised in the annealing cost.
  * Metacyclic groups Z_m x|_r Z_k are evaluated by arithmetic, not by a multiplication
    table, so switching candidates costs O(1). Matrix groups use a table.
  * Search: simulated-annealing-style moves on voltages and permutation swaps. Candidates are
    scheduled in iterative-deepening rounds, upper window (beat the reference) first.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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

#define MAXN 3200
#define MAXDEG 8
#define MAXP 8
#define MAXVV 16384
#define MAXCAND 220
#define STALL 3000

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group access */

static int N = 0, e_id = 0, gtype = 0;   /* gtype 0: metacyclic (arithmetic), 1: table */
static int mm = 1, mk = 1;
static int pw[MAXN];
static uint16_t *T = NULL;               /* table for matrix groups: T[x*N+y] = x*y */
static size_t tcap = 0;
static int *INV = NULL;                  /* inverses (table mode) */

static void alloc_group(int n) {
    size_t need = (size_t)n * (size_t)n;
    if (need > tcap) {
        free(T);
        T = malloc(sizeof(uint16_t) * need);
        tcap = need;
    }
    if (!INV) INV = malloc(sizeof(int) * MAXN);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int set_meta(int m, int k, int r) {
    int n = m * k;
    if (m < 1 || k < 1 || n > MAXN || n < 2) return 0;
    gtype = 0;
    mm = m;
    mk = k;
    N = n;
    e_id = 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    return N;
}

static inline int gmul(int x, int y) {
    if (gtype == 1) return (int)T[(size_t)x * N + y];
    int a = x / mk, b = x % mk, c = y / mk, dd = y % mk;
    int aa = (a + pw[b] * c) % mm;
    int bb = (b + dd) % mk;
    return aa * mk + bb;
}

static inline int ginv(int x) {
    if (gtype == 1) return INV[x];
    int a = x / mk, b = x % mk;
    int nb = (mk - b) % mk;
    int t = (int)((long)pw[nb] * a % mm);
    return ((mm - t) % mm) * mk + nb;
}

/* PSL(2,q) or SL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    gtype = 1;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return N;
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, P;
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return set_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_meta_cands(int P_, long N_, Cand *arr, int *cnt) {
    if (N_ < 3 || N_ > MAXN || *cnt >= MAXCAND) return;
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = 0;
    c.m = (int)N_;
    c.k = 1;
    c.r = 1;
    c.N = (int)N_;
    c.P = P_;
    arr[(*cnt)++] = c;
    for (long k = 2; k <= N_ / 3 && *cnt < MAXCAND; k++) {
        if (N_ % k) continue;
        long m = N_ / k;
        if (m < 3) continue;
        int got = 0;
        for (long r = 1; r < m && got < 2 && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand cc;
            memset(&cc, 0, sizeof cc);
            cc.type = 0;
            cc.m = (int)m;
            cc.k = (int)k;
            cc.r = (int)r;
            cc.N = (int)N_;
            cc.P = P_;
            arr[(*cnt)++] = cc;
            got++;
        }
    }
}

/* ------------------------------------------------------------ P-orbit lift state */

static int P = 1;

typedef struct {
    int pi[MAXDEG][MAXP];     /* pi[k][i]: B-orbit hit by dart k of A_i */
    int pinv[MAXDEG][MAXP];   /* pinv[k][j]: A-orbit whose dart k hits B_j */
    int vg[MAXP][MAXDEG];     /* voltage of dart (i,k) */
} State;

static State st, bst;
static int ADJ[MAXVV * MAXDEG];
static int stamp[MAXVV];
static int qv[MAXVV];
static int tick_ = 0;

/* A_i x (id i*N+x) and B_j y (id P*N + j*N + y).
   A_i x -- B_{pi_k(i)} (x*g_{i,k}) for each dart k. */
static void build_adj(void) {
    int PN = P * N;
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++) {
            int v = i * N + x;
            for (int k = 0; k < d; k++) {
                int j = st.pi[k][i];
                ADJ[v * d + k] = PN + j * N + gmul(x, st.vg[i][k]);
            }
        }
    for (int j = 0; j < P; j++)
        for (int y = 0; y < N; y++) {
            int v = PN + j * N + y;
            for (int k = 0; k < d; k++) {
                int i = st.pinv[k][j];
                int g = st.vg[i][k];
                ADJ[v * d + k] = i * N + gmul(y, ginv(g));
            }
        }
}

static int reach_count(int src, int dmax) {
    if (++tick_ == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick_ = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick_;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            const int *a = &ADJ[v * d];
            for (int k = 0; k < d; k++) {
                int u = a[k];
                if (stamp[u] != tick_) {
                    stamp[u] = tick_;
                    qv[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static long conflict_count(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++)
            for (int l = k + 1; l < d; l++)
                if (st.pi[k][i] == st.pi[l][i] && st.vg[i][k] == st.vg[i][l]) c++;
    return c;
}

/* Cost: unreached (root, vertex) pairs over the 2P automorphism-orbit roots,
   plus a heavy penalty per multi-edge conflict. Zero iff valid. */
static long cost_eval(void) {
    long VT = 2L * P * N;
    build_adj();
    long unr = 0;
    for (int i = 0; i < P; i++) {
        unr += VT - reach_count(i * N + e_id, D);
        unr += VT - reach_count(P * N + i * N + e_id, D);
    }
    return unr + conflict_count() * VT;
}

static void random_state(void) {
    for (int k = 0; k < d; k++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < P; i++) {
            st.pi[k][i] = perm[i];
            st.pinv[k][perm[i]] = i;
        }
    }
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) st.vg[i][k] = rndint(N);
}

static void propose(void) {
    if (P > 1 && rndint(2) == 0) {
        int k = rndint(d);
        int i1 = rndint(P);
        int i2 = rndint(P - 1);
        if (i2 >= i1) i2++;
        int t = st.pi[k][i1];
        st.pi[k][i1] = st.pi[k][i2];
        st.pi[k][i2] = t;
        st.pinv[k][st.pi[k][i1]] = i1;
        st.pinv[k][st.pi[k][i2]] = i2;
    } else {
        int i = rndint(P), k = rndint(d);
        st.vg[i][k] = rndint(N);
    }
}

static int climb(double until) {
    random_state();
    long cur = cost_eval(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL) {
            random_state();
            cur = cost_eval();
            best_c = cur;
            stall = 0;
            continue;
        }
        State save = st;
        propose();
        long nc = cost_eval();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            st = save;
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 4970;
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long lowV = (long)(0.87 * (double)ref);
    if (lowV < 3) lowV = 3;
    long hiV = ref + 40;
    if (hiV > moore) hiV = moore;
    if (hiV > MAXVV) hiV = MAXVV;

    static Cand all[MAXCAND];
    int nc = 0;

    /* Upper window: orders above the reference, smallest first, preferred P first. */
    static const int Pup[] = {2, 3, 4, 1, 5, 6, 8};
    for (unsigned pi_ = 0; pi_ < sizeof Pup / sizeof Pup[0]; pi_++) {
        long Pv = Pup[pi_];
        long Nlo = ref / (2 * Pv) + 1;
        long Nhi = hiV / (2 * Pv);
        for (long Nv = Nlo; Nv <= Nhi && nc < MAXCAND; Nv++)
            add_meta_cands((int)Pv, Nv, all, &nc);
    }

    /* Lower window: matrix groups first (known fallbacks), then metacyclic, descending. */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXN) continue;
            for (long Pv = 1; Pv <= MAXP && nc < MAXCAND; Pv++) {
                long V = 2 * Pv * o;
                if (V < lowV || V > ref || V > moore) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.N = (int)o;
                c.P = (int)Pv;
                all[nc++] = c;
            }
        }
    }
    static const int Plo[] = {1, 2, 3, 4, 5, 6, 8};
    for (unsigned pi_ = 0; pi_ < sizeof Plo / sizeof Plo[0]; pi_++) {
        long Pv = Plo[pi_];
        long Nhi = ref / (2 * Pv);
        long Nlo = lowV / (2 * Pv) + 1;
        for (long Nv = Nhi; Nv >= Nlo && nc < MAXCAND; Nv--)
            add_meta_cands((int)Pv, Nv, all, &nc);
    }

    double budget0 = t_end - now();
    double base_slice = budget0 / (2.0 * (nc > 0 ? nc : 1));
    if (base_slice < 0.12) base_slice = 0.12;
    if (base_slice > budget0 * 0.2) base_slice = budget0 * 0.2;

    int have = 0;
    long bestV = 0;
    Cand best;
    memset(&best, 0, sizeof best);

    /* Iterative deepening: each round gives every candidate that could still beat the
       current best a slice; the slice doubles each round. */
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < nc; i++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &all[i];
            long VV = 2L * c->P * c->N;
            if (VV <= bestV || VV > moore || VV > MAXVV) continue;
            if (apply_cand(c) <= 0) continue;
            P = c->P;
            double slice = base_slice * (double)(1 << round);
            if (slice > rem) slice = rem;
            if (climb(now() + slice)) {
                have = 1;
                bestV = VV;
                best = *c;
                bst = st;
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (apply_cand(&best) <= 0) { print_complete(); return 0; }
    P = best.P;
    st = bst;
    if (cost_eval() != 0) { print_complete(); return 0; }

    int PN = P * N;
    printf("%ld %ld\n", 2L * PN, (long)PN * d);
    for (int v = 0; v < PN; v++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", v, ADJ[v * d + k]);
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    # Use most of the case's time for the C search; keep a margin for compile, I/O and checks.
    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = int(REF_VERTICES.get((d, D), best[0]))
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best

import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-lift search over FINITE GROUPS given by their right-regular permutations.
#
# Structure: K base vertices A_i and K base vertices B_p. Each layer l is a
# bijection lay[l][i] = p, with a voltage vol[l][i] in G. Vertex (A_i, x) is
# joined to (B_p, x*s). Every vertex has degree DEG and the graph is bipartite.
# The group acts by left multiplication, so the diameter check only needs the
# 2K block representatives.
#
# Groups are non-metacyclic where possible: PSL/PGL/SL(2,p) and direct products
# of them with cyclic groups, plus a few metacyclic groups. The C side receives
# only generator permutations and builds the multiplication table itself.
# A bandit over (group, K) arms, annealing with defect targeting, and iterated
# local search from the best near miss drive the search.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 8
#define PEN 1000
#define GCAP 3000

typedef uint16_t mask_t;

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int DEG, DIAM, CAP;
static double TL, tstart;
static uint8_t POP[65536];

static int NG;
static int *gG, *gNg, *gOff, *gok, *gperm;
static int MAXG;
static int *mul, *invv, *ordv, *parv, *genv, *seenv;
static int cur_g = -1, G = 0;

static int K, N;
static int *lay, *vol, *nbr;      /* lay/vol index: l*KMAX + i */
static mask_t *bufA, *bufB, *tmpb, *cur, *scr;
static mask_t FULL;
static int64_t LASTCOST;
static int timed_out;

static int have_near, nr_g, nr_K, nr_N;
static int64_t nr_cost;
static int *nr_lay, *nr_vol;

static int NA;
static int *arm_g, *arm_k, *feas;
static double *tr_, *wn_;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

/* Build the multiplication table of group g from its right-regular generator
   permutations. Element 0 is the identity. Returns 1 on success. */
static int set_group(int g) {
    if (g == cur_g) return 1;
    if (!gok[g]) return 0;
    int n = gG[g], ng = gNg[g];
    const int *perm = gperm + gOff[g];
    if (n > MAXG) return 0;
    for (int x = 0; x < n; x++) seenv[x] = 0;
    int cnt = 0;
    ordv[cnt++] = 0;
    seenv[0] = 1;
    parv[0] = -1;
    genv[0] = -1;
    for (int h = 0; h < cnt; h++) {
        int x = ordv[h];
        for (int j = 0; j < ng; j++) {
            int z = perm[j * n + x];
            if (z < 0 || z >= n) { gok[g] = 0; return 0; }
            if (!seenv[z]) {
                if (cnt >= n) { gok[g] = 0; return 0; }
                seenv[z] = 1;
                parv[z] = x;
                genv[z] = j;
                ordv[cnt++] = z;
            }
        }
    }
    if (cnt != n) { gok[g] = 0; return 0; }
    for (int x = 0; x < n; x++) {
        int *row = mul + (size_t)x * n;
        row[0] = x;
        for (int h = 1; h < n; h++) {
            int y = ordv[h];
            row[y] = perm[genv[y] * n + row[parv[y]]];
        }
    }
    for (int x = 0; x < n; x++) {
        int *row = mul + (size_t)x * n;
        invv[x] = 0;
        for (int y = 0; y < n; y++)
            if (row[y] == 0) { invv[x] = y; break; }
    }
    G = n;
    cur_g = g;
    return 1;
}

static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int p = lay[l * KMAX + i];
        int s = vol[l * KMAX + i];
        int Ab = i * G, Bb = (K + p) * G;
        for (int g = 0; g < G; g++) {
            int a = Ab + g;
            int b = Bb + mul[(size_t)g * G + s];
            nbr[(size_t)a * DEG + l] = b;
            nbr[(size_t)b * DEG + l] = a;
        }
    }
}

/* out[v] = bitmask of block representatives within DIAM steps of v. */
static void compute_reach(mask_t *out) {
    int n = N;
    memset(out, 0, sizeof(mask_t) * (size_t)n);
    for (int b = 0; b < 2 * K; b++) out[(size_t)b * G] = (mask_t)(1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            mask_t x = out[v];
            const int *row = nbr + (size_t)v * DEG;
            for (int l = 0; l < DEG; l++) x |= out[row[l]];
            tmpb[v] = x;
            if (x != out[v]) changed = 1;
        }
        memcpy(out, tmpb, sizeof(mask_t) * (size_t)n);
        if (!changed) break;
    }
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 1; l < DEG; l++) {
            int p = lay[l * KMAX + i], s = vol[l * KMAX + i];
            for (int f = 0; f < l; f++)
                if (lay[f * KMAX + i] == p && vol[f * KMAX + i] == s) {
                    dup++;
                    break;
                }
        }
    return dup;
}

static int64_t total_cost(const mask_t *r) {
    int64_t s = 0;
    int tot = 2 * K;
    for (int v = 0; v < N; v++) s += tot - POP[r[v]];
    return s + (int64_t)PEN * dupcount();
}

static int run_trial(int iters, int patience, int reinit) {
    timed_out = 0;
    if (reinit) {
        for (int l = 0; l < DEG; l++) {
            int perm[KMAX];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) lay[l * KMAX + i] = perm[i];
        }
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) vol[l * KMAX + i] = rndint(G);
    }
    for (int l = 0; l < DEG; l++) rebuild_layer(l);
    compute_reach(cur);
    int64_t cost = total_cost(cur);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int64_t best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        int l = rndint(DEG);
        int sl[KMAX], sv[KMAX];
        for (int i = 0; i < K; i++) {
            sl[i] = lay[l * KMAX + i];
            sv[i] = vol[l * KMAX + i];
        }
        if (K >= 2 && rnd01() < 0.25) {
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tp = lay[l * KMAX + i1];
            lay[l * KMAX + i1] = lay[l * KMAX + i2];
            lay[l * KMAX + i2] = tp;
        } else {
            int i = -1, u = -1;
            if (rnd01() < 0.4) {
                int cnt = 0;
                for (int v = 0; v < N; v++)
                    if (cur[v] != FULL) {
                        cnt++;
                        if (rndint(cnt) == 0) u = v;
                    }
            }
            if (u >= 0) {
                int b = u / G;
                if (b < K) {
                    i = b;
                } else {
                    int p = b - K;
                    for (int j = 0; j < K; j++)
                        if (lay[l * KMAX + j] == p) { i = j; break; }
                }
            }
            if (i < 0) i = rndint(K);
            int nw = rndint(G);
            if (nw == vol[l * KMAX + i]) continue;
            vol[l * KMAX + i] = nw;
        }
        rebuild_layer(l);
        compute_reach(scr);
        int64_t c2 = total_cost(scr);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            mask_t *tb = cur;
            cur = scr;
            scr = tb;
            cost = c2;
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
            }
        } else {
            for (int i = 0; i < K; i++) {
                lay[l * KMAX + i] = sl[i];
                vol[l * KMAX + i] = sv[i];
            }
            rebuild_layer(l);
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

static void save_near(int g) {
    have_near = 1;
    nr_g = g;
    nr_K = K;
    nr_N = N;
    nr_cost = LASTCOST;
    memcpy(nr_lay, lay, sizeof(int) * (size_t)DEG * KMAX);
    memcpy(nr_vol, vol, sizeof(int) * (size_t)DEG * KMAX);
}

static int pick_arm(int64_t found) {
    int nf = 0;
    double ttot = 0.0;
    for (int a = 0; a < NA; a++) {
        int g = arm_g[a];
        if (!gok[g]) continue;
        int64_t Nn = 2LL * arm_k[a] * gG[g];
        if (Nn <= found || Nn > CAP) continue;
        feas[nf++] = a;
        ttot += tr_[a];
    }
    if (nf == 0) return -1;
    if (rnd01() < 0.15) return feas[rndint(nf)];
    int bi = feas[0];
    double bv = -1e300;
    for (int i = 0; i < nf; i++) {
        int a = feas[i];
        double v = (wn_[a] + 1.0) / (tr_[a] + 2.0)
                 + 0.3 * sqrt(log(ttot + 2.0) / (tr_[a] + 1.0))
                 + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bi = a;
        }
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D best0 cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 65536; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DEG > 64 || DIAM < 3 || CAP < 8 || CAP > 200000) {
        printf("0 0\n");
        return 0;
    }

    int NGr = 0, M = 0;
    if (scanf("%d %d", &NGr, &M) != 2) { NGr = 0; M = 0; }
    if (M < 0) M = 0;
    int *pv = malloc(sizeof(int) * (size_t)(2 * M + 2));
    if (!pv) { printf("0 0\n"); return 0; }
    for (int i = 0; i < 2 * M; i++) {
        if (scanf("%d", &pv[i]) != 1) { M = i / 2; break; }
    }

    gG = malloc(sizeof(int) * (size_t)(NGr + 1));
    gNg = malloc(sizeof(int) * (size_t)(NGr + 1));
    gOff = malloc(sizeof(int) * (size_t)(NGr + 1));
    gok = malloc(sizeof(int) * (size_t)(NGr + 1));
    gperm = malloc(sizeof(int) * (size_t)(M + 1));
    if (!gG || !gNg || !gOff || !gok || !gperm) { printf("0 0\n"); return 0; }

    NG = 0;
    MAXG = 2;
    int total = 0, pos = 0;
    while (NG < NGr && pos < M) {
        int n = pv[2 * pos], ng = pv[2 * pos + 1];
        if (n < 2 || n > GCAP || ng < 1 || ng > 4) break;
        if (pos + 1 + n * ng > M) break;
        gG[NG] = n;
        gNg[NG] = ng;
        gOff[NG] = total;
        gok[NG] = 1;
        for (int k = 0; k < n * ng; k++)
            gperm[total + k] = pv[2 * (pos + 1 + k) + 1];
        total += n * ng;
        pos += 1 + n * ng;
        if (n > MAXG) MAXG = n;
        NG++;
    }
    if (NG == 0) {
        printf("0 0\n");
        return 0;
    }

    mul = malloc(sizeof(int) * (size_t)MAXG * MAXG);
    invv = malloc(sizeof(int) * (size_t)MAXG);
    ordv = malloc(sizeof(int) * (size_t)MAXG);
    parv = malloc(sizeof(int) * (size_t)MAXG);
    genv = malloc(sizeof(int) * (size_t)MAXG);
    seenv = malloc(sizeof(int) * (size_t)MAXG);
    lay = calloc((size_t)DEG * KMAX, sizeof(int));
    vol = calloc((size_t)DEG * KMAX, sizeof(int));
    nr_lay = calloc((size_t)DEG * KMAX, sizeof(int));
    nr_vol = calloc((size_t)DEG * KMAX, sizeof(int));
    nbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    bufA = malloc(sizeof(mask_t) * (size_t)CAP);
    bufB = malloc(sizeof(mask_t) * (size_t)CAP);
    tmpb = malloc(sizeof(mask_t) * (size_t)CAP);
    int *bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    NA = NG * KMAX;
    arm_g = malloc(sizeof(int) * (size_t)NA);
    arm_k = malloc(sizeof(int) * (size_t)NA);
    feas = malloc(sizeof(int) * (size_t)NA);
    tr_ = calloc((size_t)NA, sizeof(double));
    wn_ = calloc((size_t)NA, sizeof(double));
    if (!mul || !invv || !ordv || !parv || !genv || !seenv || !lay || !vol ||
        !nr_lay || !nr_vol || !nbr || !bufA || !bufB || !tmpb || !bestnbr ||
        !arm_g || !arm_k || !feas || !tr_ || !wn_) {
        printf("0 0\n");
        return 0;
    }
    cur = bufA;
    scr = bufB;

    for (int g = 0; g < NG; g++)
        if (!set_group(g)) gok[g] = 0;
    for (int a = 0; a < NA; a++) {
        arm_g[a] = a / KMAX;
        arm_k[a] = a % KMAX + 1;
    }

    int64_t found = best0;
    int have_best = 0, best_N = 0, best_A = 0;
    have_near = 0;

    while (elapsed() < TL && found < CAP) {
        int ag = -1, ak = 0, arm = -1, ok = 0;
        if (have_near && nr_N > found && rnd01() < 0.4) {
            /* Iterated local search: kick the saved near miss and re-anneal. */
            if (!set_group(nr_g)) {
                have_near = 0;
                continue;
            }
            K = nr_K;
            N = 2 * K * G;
            FULL = (mask_t)((1u << (2 * K)) - 1u);
            memcpy(lay, nr_lay, sizeof(int) * (size_t)DEG * KMAX);
            memcpy(vol, nr_vol, sizeof(int) * (size_t)DEG * KMAX);
            int kicks = 2 + rndint(4);
            for (int q = 0; q < kicks; q++) {
                int l = rndint(DEG), i = rndint(K);
                vol[l * KMAX + i] = rndint(G);
            }
            ag = nr_g;
            ak = nr_K;
            ok = run_trial(3000, 1000, 0);
        } else {
            arm = pick_arm(found);
            if (arm < 0) break;
            ag = arm_g[arm];
            ak = arm_k[arm];
            tr_[arm] += 1.0;
            if (!set_group(ag)) continue;
            K = ak;
            N = 2 * K * G;
            FULL = (mask_t)((1u << (2 * K)) - 1u);
            ok = run_trial(4000, 1200, 1);
        }
        (void)ak;

        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 &&
               elapsed() < TL) {
            ok = run_trial(6000, 2000, 0);
            extra++;
        }
        if (!ok && !timed_out && LASTCOST > 0) {
            if (!have_near || LASTCOST < nr_cost || nr_N <= found) save_near(ag);
        }
        if (ok) {
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_N = N;
            best_A = K * G;
            have_best = 1;
            have_near = 0;
            if (arm >= 0) wn_[arm] += 1.0;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int m = best_A * DEG;
    printf("%d %d\n", best_N, m);
    for (int v = 0; v < best_A; v++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", v, bestnbr[(size_t)v * DEG + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group generators (right-regular permutations). Each group is (order, gens),
# where gens[j][x] = index of x * s_j, and element 0 is the identity.
# ----------------------------------------------------------------------------

def _prime_factors(n):
    fs = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            fs.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        fs.append(n)
    return fs


def _primroot(p):
    fs = _prime_factors(p - 1)
    for w in range(2, p):
        if all(pow(w, (p - 1) // q, p) != 1 for q in fs):
            return w
    return 1


def _perm_sd(m, k, r):
    """Metacyclic group Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e)."""
    n = m * k
    pw = [pow(r, b, m) for b in range(k)]
    p0, p1 = [], []
    for x in range(n):
        a, b = divmod(x, k)
        p0.append(((a + pw[b]) % m) * k + b)
        p1.append(a * k + (b + 1) % k)
    return n, [p0, p1]


def _perm_mat(p, kind):
    """PSL, PGL or SL(2,p) acting on itself by right multiplication."""
    def mul(M, N):
        a, b, c, d = M
        e, f, g, h = N
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)

    def norm(M):
        if kind == 'PGL':
            for x in M:
                if x:
                    iv = pow(x, p - 2, p)
                    return tuple(y * iv % p for y in M)
        if kind == 'PSL':
            return min(M, tuple((-y) % p for y in M))
        return M

    gens = [(1, 1, 0, 1), (0, p - 1, 1, 0)]
    if kind == 'PGL':
        gens.append((_primroot(p), 0, 0, 1))
    gens = [norm(g) for g in gens]
    I = norm((1, 0, 0, 1))
    elems = [I]
    idx = {I: 0}
    h = 0
    while h < len(elems):
        x = elems[h]
        h += 1
        for s in gens:
            z = norm(mul(x, s))
            if z not in idx:
                idx[z] = len(elems)
                elems.append(z)
    perms = [[idx[norm(mul(x, s))] for x in elems] for s in gens]
    return len(elems), perms


def _perm_times_cyclic(n0, gens0, c):
    """Direct product G0 x Z_c, element (x, w) coded as x*c + w."""
    n = n0 * c
    gens = []
    for pm in gens0:
        newp = [0] * n
        for x in range(n0):
            for w in range(c):
                newp[x * c + w] = pm[x] * c + w
        gens.append(newp)
    cyc = [0] * n
    for x in range(n0):
        for w in range(c):
            cyc[x * c + w] = x * c + (w + 1) % c
    gens.append(cyc)
    return n, gens


def _group_pool(rng, lo=200, hi=1400):
    """Candidate groups with order in [lo, hi], shuffled and capped."""
    cands = []
    specs = [(5, 'PSL'), (7, 'PSL'), (7, 'PGL'), (7, 'SL'),
             (11, 'PSL'), (11, 'PGL'), (11, 'SL'), (13, 'PSL'), (13, 'SL')]
    for p, kind in specs:
        n0, g0 = _perm_mat(p, kind)
        if n0 > hi:
            continue
        for c in (1, 2, 3, 4, 5, 6, 7, 8, 10, 12):
            n = n0 * c
            if n < lo or n > hi:
                continue
            cands.append((n, g0) if c == 1 else _perm_times_cyclic(n0, g0, c))

    seen = set()
    sd = 0
    for _ in range(4000):
        if sd >= 8:
            break
        k = rng.randint(2, 12)
        mlo = max(3, -(-lo // k))
        mhi = hi // k
        if mhi < mlo:
            continue
        m = rng.randint(mlo, mhi)
        r = rng.choice([1, m - 1, rng.randrange(1, m)])
        if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
            continue
        key = (m, k, r)
        if key in seen:
            continue
        seen.add(key)
        cands.append(_perm_sd(m, k, r))
        sd += 1

    rng.shuffle(cands)
    return cands[:16]


def _encode_pool(pool):
    """Stdin payload: header pair (order, #gens) then gens as (x, perm[x]) pairs."""
    edges = []
    for n, gens in pool:
        edges.append((n, len(gens)))
        for pm in gens:
            edges.extend((x, pm[x]) for x in range(n))
    return len(pool), edges


# ----------------------------------------------------------------------------
# Exact construction for the D = 3 case (projective plane incidence graphs).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main build: exact start if available, then the group-lift search in C.
# K_{d,d} is the always-valid fallback for D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        cap = min(lib.moore_bound(d, D), 60000)
        if cap > best_n:
            budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
            remaining = start + budget - time.monotonic()
            if remaining > 1.5:
                rng = random.Random(int(seed) * 1000003 + d * 31 + D)
                pool = _group_pool(rng)
                if pool:
                    ng, edges = _encode_pool(pool)
                    try:
                        text = lib.run_c(
                            C_SOURCE,
                            [d, D, best_n, cap, int(seed) & 0x7FFFFFFF,
                             round(max(0.5, remaining - 2.0), 2)],
                            stdin_graph=(ng, edges),
                            timeout=remaining + 3.0)
                        n2, e2 = lib.parse_graph_text(text)
                        consider(n2, e2)
                    except Exception:
                        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

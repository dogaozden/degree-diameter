/* b02: Haar graphs H(G,S) on G = GF(2^15) x| Z_151, (a,j)(b,l) = (a + z^j b, j + l),
 * z = g^217 of order 151 (g = x primitive in GF(2)[x]/(x^15+x+1)).
 * Field automorphism orbits: alpha_r(a,j) = (a^(2^r), 2^r j); order 5 for r = 3, order 3 for r = 5.
 *
 * usage: frob search K R M INCL SECS SEED OUT
 *   S = (INCL ? {e} : {}) + M alpha_R-orbits of size K (K = 5 for R = 3, K = 3 for R = 5).
 *   cost = number of B-vertices at distance > 11 from (e,A)   (0 => diameter <= 12 by the transitivity argument;
 *   a cost-0 S is then checked with the full eccentricity test below and written to OUT as "a j" lines).
 * usage: frob check FILE   (FILE: lines "a j", the S of a solution; full BFS from (e,A) and (e,B)).
 *
 * Exact diameter: right multiplication is transitive on each side, so diam = max(ecc(e,A), ecc(e,B)).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define FQ 32768u
#define QM 32767u
#define NZ 151u
#define NG (FQ * NZ)
#define NBITS (2u * NG)

static uint16_t expt[2 * QM];
static uint16_t logt[FQ];
static uint32_t ezt[NZ];     /* log_g(z^j) = 217 j mod QM */
static uint64_t *vis;
static uint32_t *q;
static uint32_t lev[256];
static int nl;
static uint32_t tail;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void init_field(void) {
    uint32_t v = 1;
    memset(logt, 0xff, sizeof logt);
    for (uint32_t i = 0; i < QM; i++) {
        expt[i] = (uint16_t)v;
        if (logt[v] != 0xffff) { fprintf(stderr, "not primitive at %u\n", i); exit(1); }
        logt[v] = (uint16_t)i;
        v <<= 1;
        if (v & FQ) v ^= FQ | 3u; /* x^15 = x + 1 */
    }
    if (v != 1) { fprintf(stderr, "period error\n"); exit(1); }
    for (uint32_t i = QM; i < 2 * QM; i++) expt[i] = expt[i - QM];
    for (uint32_t j = 0; j < NZ; j++) ezt[j] = (217u * j) % QM;
}

/* element index: (j << 15) | a  ;  identity = 0 */
static inline uint32_t gmul(uint32_t s, uint32_t g) {
    uint32_t c = s & (FQ - 1), k = s >> 15;
    uint32_t b = g & (FQ - 1), l = g >> 15;
    uint32_t a = c ^ (b ? expt[ezt[k] + logt[b]] : 0u);
    uint32_t m = k + l; if (m >= NZ) m -= NZ;
    return (m << 15) | a;
}

static uint32_t inv(uint32_t s) {
    uint32_t c = s & (FQ - 1), k = s >> 15;
    uint32_t a = c ? expt[((QM - ezt[k]) % QM) + logt[c]] : 0u;
    uint32_t m = (NZ - k) % NZ;
    return (m << 15) | a;
}

/* alpha_r(a,j) = (a^(2^r), 2^r j) */
static inline uint32_t alpha(uint32_t y, int r) {
    uint32_t c = y & (FQ - 1), k = y >> 15;
    uint32_t c2 = c ? expt[(logt[c] * (1u << r)) % QM] : 0u;
    uint32_t k2 = (k * (1u << r)) % NZ;
    return (k2 << 15) | c2;
}

static inline int bit(uint32_t v) { return (vis[v >> 6] >> (v & 63)) & 1; }
static inline void setb(uint32_t v) { vis[v >> 6] |= (uint64_t)1 << (v & 63); }

/* BFS from start over H(G,S): A-vertex g (index < NG) ~ B-vertex NG + s*g; B-vertex NG+h ~ A-vertex s^-1 h.
 * Levels: level k = [lev[k], lev[k+1]), nl = number of levels. Stops after level maxd. */
static void bfs(const uint32_t *S, const uint32_t *Si, int nS, uint32_t start, int maxd) {
    memset(vis, 0, (NBITS / 64 + 1) * sizeof(uint64_t));
    tail = 0;
    q[tail++] = start; setb(start);
    lev[0] = 0; lev[1] = 1; nl = 1;
    while (nl - 1 < maxd) {
        uint32_t ls = lev[nl - 1], le = lev[nl];
        for (uint32_t i = ls; i < le; i++) {
            uint32_t v = q[i];
            if (v < NG) {
                for (int k = 0; k < nS; k++) {
                    uint32_t w = NG + gmul(S[k], v);
                    if (!bit(w)) { setb(w); q[tail++] = w; }
                }
            } else {
                uint32_t h = v - NG;
                for (int k = 0; k < nS; k++) {
                    uint32_t w = gmul(Si[k], h);
                    if (!bit(w)) { setb(w); q[tail++] = w; }
                }
            }
        }
        if (tail == le) break;
        nl++; lev[nl] = tail;
    }
}

static int64_t eval_cost(const uint32_t *S, int nS) {
    uint32_t Si[16];
    for (int k = 0; k < nS; k++) Si[k] = inv(S[k]);
    bfs(S, Si, nS, 0, 11);
    uint64_t cntB = 0;
    for (int k = 1; k <= 11 && k < nl; k += 2) cntB += lev[k + 1] - lev[k];
    return (int64_t)NG - (int64_t)cntB;
}

/* orbit of (a,j) under alpha_r of size K; S = [e] + orbits; returns nS or -1 */
static int build_S(const uint32_t *ra, const uint32_t *rj, int M, int K, int incl, int r, uint32_t *S) {
    int n = 0;
    if (incl) S[n++] = 0;
    for (int o = 0; o < M; o++) {
        uint32_t x = (rj[o] << 15) | ra[o], y = x;
        for (int i = 0; i < K; i++) {
            S[n++] = y;
            y = alpha(y, r);
            if (i < K - 1 && y == x) return -1;
        }
        if (y != x) return -1;
    }
    for (int i = 0; i < n; i++)
        for (int k = 0; k < i; k++)
            if (S[i] == S[k]) return -1;
    return n;
}

static void full_check(const uint32_t *S, int nS) {
    uint32_t Si[16];
    for (int k = 0; k < nS; k++) Si[k] = inv(S[k]);
    bfs(S, Si, nS, 0, 1000000);
    int eA = nl - 1; uint32_t visA = tail;
    bfs(S, Si, nS, NG, 1000000);
    int eB = nl - 1; uint32_t visB = tail;
    printf("FULLCHECK nS=%d  ecc(e,A)=%d (visited %u of %u)  ecc(e,B)=%d (visited %u of %u)  diameter=%d  %s\n",
           nS, eA, visA, 2 * NG, eB, visB, 2 * NG, eA > eB ? eA : eB,
           (visA == 2 * NG && visB == 2 * NG && (eA > eB ? eA : eB) <= 12) ? "VALID(D<=12)" : "not valid");
    fflush(stdout);
}

static void write_S(const char *path, const uint32_t *S, int nS) {
    FILE *f = fopen(path, "w");
    if (!f) { perror("open"); return; }
    fprintf(f, "# Haar graph H(G,S), G = GF(2^15) x| Z_151, (a,j)(b,l)=(a+z^j b, j+l), z=g^217, g: x^15+x+1 primitive\n");
    fprintf(f, "# vertices 2*%u, degree %d; S lines \"a j\" (a in GF(2^15) as 15-bit int, polynomial basis of x)\n", NG, nS);
    for (int k = 0; k < nS; k++) fprintf(f, "%u %u\n", S[k] & (FQ - 1), S[k] >> 15);
    fclose(f);
}

static void print_S(const uint32_t *S, int nS) {
    for (int k = 0; k < nS; k++) printf(" (%u,%u)", S[k] & (FQ - 1), S[k] >> 15);
    printf("\n");
}

int main(int argc, char **argv) {
    init_field();
    vis = malloc((NBITS / 64 + 2) * sizeof(uint64_t));
    q = malloc((size_t)NBITS * sizeof(uint32_t));
    if (!vis || !q) { fprintf(stderr, "alloc\n"); return 1; }

    if (argc >= 3 && strcmp(argv[1], "check") == 0) {
        FILE *f = fopen(argv[2], "r");
        if (!f) { perror("open"); return 1; }
        uint32_t S[16]; int n = 0; char line[256];
        while (fgets(line, sizeof line, f)) {
            if (line[0] == '#' || line[0] == '\n') continue;
            unsigned a, j;
            if (sscanf(line, "%u %u", &a, &j) == 2) S[n++] = (j << 15) | a;
        }
        fclose(f);
        printf("read %d elements\n", n);
        full_check(S, n);
        return 0;
    }

    if (argc < 9 || strcmp(argv[1], "search") != 0) {
        fprintf(stderr, "usage: frob search K R M INCL SECS SEED OUT | frob check FILE\n");
        return 1;
    }
    int K = atoi(argv[2]), R = atoi(argv[3]), M = atoi(argv[4]), INCL = atoi(argv[5]);
    int SECS = atoi(argv[6]);
    rs ^= (uint64_t)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *OUT = argv[8];
    int Delta = M * K + INCL;

    uint32_t ra[8], rj[8], S[16];
    long nev = 0, nbad = 0;
    long hist[64]; memset(hist, 0, sizeof hist);
    int64_t best = -1; uint32_t bra[8], brj[8];
    time_t t0 = time(NULL);
    int done = 0;

    int resumed = 0;
    if (getenv("START")) {  /* resume: M lines "a j" = orbit representatives */
        FILE *sf = fopen(getenv("START"), "r");
        if (sf) { for (int o = 0; o < M; o++) if (fscanf(sf, "%u %u", &ra[o], &rj[o]) != 2) break; fclose(sf);
            int n0 = build_S(ra, rj, M, K, INCL, R, S);
            if (n0 == Delta) { resumed = 1; best = eval_cost(S, n0); nev++; memcpy(bra, ra, sizeof ra); memcpy(brj, rj, sizeof rj);
                printf("resumed from %s: cost %lld\n", getenv("START"), (long long)best); } }
    }
    /* phase 1: uniform random orbit representatives (half the time) */
    while (!resumed && !done && (long)(time(NULL) - t0) < (getenv("RANDFRAC") ? atof(getenv("RANDFRAC")) : 0.5) * SECS) {
        for (int o = 0; o < M; o++) { ra[o] = rnd() & (FQ - 1); rj[o] = rnd() % NZ; }
        int n = build_S(ra, rj, M, K, INCL, R, S);
        if (n != Delta) { nbad++; continue; }
        int64_t c = eval_cost(S, n);
        nev++;
        if (c < 64) hist[c]++; else hist[63]++;
        if (best < 0 || c < best) { best = c; memcpy(bra, ra, sizeof ra); memcpy(brj, rj, sizeof rj); }
        if (c == 0) {
            printf("COST 0 at eval %ld (random phase) S:", nev); print_S(S, n);
            full_check(S, n);
            write_S(OUT, S, n);
            done = 1;
        }
    }
    printf("random phase: evals %ld (rejected %ld), best cost %lld\n", nev, nbad, (long long)best);
    printf("cost histogram (bins 0..15, >=16 in last): ");
    for (int c = 0; c < 16; c++) printf("%ld ", hist[c]);
    printf("| >=16: %ld\n", hist[63]);
    fflush(stdout);

    /* phase 2: annealing over the orbit representatives, started from the best random state */
    if (!done && best >= 0) {
        int64_t cur = best;
        memcpy(ra, bra, sizeof ra); memcpy(rj, brj, sizeof rj);
        double T = getenv("TEMP_T") ? atof(getenv("TEMP_T")) : 2.0;
        int64_t sbest = best;
        long acc = 0;
        while (!done && (long)(time(NULL) - t0) < SECS) {
            uint32_t na[8], nj[8];
            memcpy(na, ra, sizeof na); memcpy(nj, rj, sizeof nj);
            int o = (int)(rnd() % M);
            uint64_t u = rnd() % 100;
            if (u < 50) na[o] ^= 1u << (rnd() % 15);
            else if (u < 80) nj[o] = (nj[o] + (rnd() & 1 ? 1 : NZ - 1)) % NZ;
            else { na[o] = rnd() & (FQ - 1); nj[o] = rnd() % NZ; }
            int n = build_S(na, nj, M, K, INCL, R, S);
            if (n != Delta) continue;
            int64_t c = eval_cost(S, n);
            nev++;
            double r01 = (double)(rnd() % 1000000) / 1e6;
            if (c <= cur || r01 < __builtin_exp(-(double)(c - cur) / T)) {
                memcpy(ra, na, sizeof na); memcpy(rj, nj, sizeof nj);
                cur = c; acc++;
            }
            if (c < sbest) { sbest = c; memcpy(bra, na, sizeof na); memcpy(brj, nj, sizeof nj); best = c; }
            if (c == 0) {
                printf("COST 0 at eval %ld (anneal) S:", nev); print_S(S, n);
                full_check(S, n);
                write_S(OUT, S, n);
                done = 1;
            }
        }
        printf("anneal: evals %ld total, accepted %ld, best cost %lld, final cost %lld\n",
               nev, acc, (long long)sbest, (long long)cur);
    }
    if (best >= 0) { printf("BESTREP"); for (int o = 0; o < M; o++) printf(" %u %u", bra[o], brj[o]); printf("  (best %lld)\n", (long long)best); }
    if (!done) printf("no cost-0 S found in %d s (evals %ld)\n", SECS, nev);
    return 0;
}

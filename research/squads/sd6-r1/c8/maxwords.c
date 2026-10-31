/* maxwords.c - card c8 (squad sd6-r1): maximize the number of distinct words
 * |S S^-1 S S^-1 S| over 7-subsets S of a finite group G (|G| >= 4797 wanted).
 *
 * Words: all 7^5 tuples s1 s2^-1 s3 s4^-1 s5 (computed as Q.S with Q = (S S^-1)(S S^-1)).
 * Invariance: |W(gS)| = |W(Sg)| = |W(S)|, so the identity can be kept in S (WLOG); FIXID is always on.
 *
 * Groups (P prime): GROUP="sl p" | "pgl p" | "psl p" (PSL(2,p) for odd p) | "agl q" (AGL(1,q), x -> ax+b),
 * optionally times a cyclic factor Z_ZM (env ZM, default 1).
 *
 * Env: GROUP (default "sl 17"), ZM (1), SECS (total annealing seconds, 60), RUNS (3), SEED (1),
 *      T0 (4.0), T1 (0.2), CHECK (1 = brute-force check of the fast count on the final sets), OUT (optional file).
 * Build: cc -O2 -o maxwords maxwords.c -lm
 * Output: one RESULT line (best coverage, uncovered = N - best, empirical random mean coverage) and the best S.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define K 7
typedef struct { int a, b, c, d, z; } El;

static int KIND = -1; /* 0 SL, 1 PGL, 2 PSL, 3 AGL */
static int P, MZ = 1, N, ID;
static El *E;
static int *IDX;
static int64_t B0;
static uint16_t *MT, *RT; /* MT[x*N+y] = x*y ; RT[y*N+x] = x*y */
static int *INV;
static uint32_t *stQ, *stW;
static uint32_t stc = 0;
static int *Ql;

static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int md(long x) { x %= P; if (x < 0) x += P; return (int)x; }
static int invp(int a) { long r = 1, b = a; int e = P - 2; while (e) { if (e & 1) r = r * b % P; b = b * b % P; e >>= 1; } return (int)r; }

static int64_t keyof(const El *e) {
    int64_t k0;
    if (KIND == 3) k0 = (int64_t)e->a * P + e->b;
    else k0 = (((int64_t)e->a * P + e->b) * P + e->c) * P + e->d;
    return k0 * MZ + e->z;
}

static void canon(El *e) {
    if (KIND == 1) { /* PGL: first nonzero entry becomes 1 */
        int f = 0, v[4] = {e->a, e->b, e->c, e->d};
        for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
        if (f > 1) {
            int iv = invp(f);
            e->a = md((long)e->a * iv); e->b = md((long)e->b * iv);
            e->c = md((long)e->c * iv); e->d = md((long)e->d * iv);
        }
    } else if (KIND == 2) { /* PSL: representative min(M, -M) */
        int x[4] = {e->a, e->b, e->c, e->d};
        int y[4] = {md(-e->a), md(-e->b), md(-e->c), md(-e->d)};
        for (int i = 0; i < 4; i++) {
            if (x[i] != y[i]) {
                if (y[i] < x[i]) { e->a = y[0]; e->b = y[1]; e->c = y[2]; e->d = y[3]; }
                break;
            }
        }
    }
}

static int valid(const El *e) {
    if (KIND == 3) return e->a != 0;
    long det = ((long)e->a * e->d - (long)e->b * e->c) % P;
    if (det < 0) det += P;
    if (KIND == 1) return det != 0;
    return det == 1;
}

static El mul(const El *x, const El *y) {
    El r;
    if (KIND == 3) {
        r.a = md((long)x->a * y->a);
        r.b = md((long)x->a * y->b + x->b);
        r.c = r.d = 0;
    } else {
        r.a = md((long)x->a * y->a + (long)x->b * y->c);
        r.b = md((long)x->a * y->b + (long)x->b * y->d);
        r.c = md((long)x->c * y->a + (long)x->d * y->c);
        r.d = md((long)x->c * y->b + (long)x->d * y->d);
    }
    r.z = (x->z + y->z) % MZ;
    canon(&r);
    return r;
}

static void decode(int64_t k, El *e) {
    e->z = (int)(k % MZ);
    int64_t k0 = k / MZ;
    if (KIND == 3) { e->a = (int)(k0 / P); e->b = (int)(k0 % P); e->c = e->d = 0; return; }
    e->d = (int)(k0 % P); k0 /= P;
    e->c = (int)(k0 % P); k0 /= P;
    e->b = (int)(k0 % P); k0 /= P;
    e->a = (int)(k0 % P);
}

static void build(void) {
    B0 = (KIND == 3) ? (int64_t)P * P : (int64_t)P * P * P * P;
    int64_t KS = B0 * MZ;
    IDX = malloc(sizeof(int) * (size_t)KS);
    E = malloc(sizeof(El) * (size_t)KS);
    N = 0;
    for (int64_t k = 0; k < KS; k++) {
        IDX[k] = -1;
        El e;
        decode(k, &e);
        if (!valid(&e)) continue;
        El c = e;
        canon(&c);
        if (c.a != e.a || c.b != e.b || c.c != e.c || c.d != e.d) continue;
        IDX[k] = N;
        E[N++] = e;
    }
    ID = -1;
    for (int i = 0; i < N; i++) {
        El *e = &E[i];
        if (e->z) continue;
        if (KIND == 3) { if (e->a == 1 && e->b == 0) ID = i; }
        else if (e->a == 1 && e->b == 0 && e->c == 0 && e->d == 1) ID = i;
    }
    if (N >= 65536 || ID < 0) { fprintf(stderr, "bad group build N=%d ID=%d\n", N, ID); exit(1); }
    MT = malloc(sizeof(uint16_t) * (size_t)N * N);
    RT = malloc(sizeof(uint16_t) * (size_t)N * N);
    INV = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            El pr = mul(&E[i], &E[j]);
            int idx = IDX[keyof(&pr)];
            if (idx < 0) { fprintf(stderr, "closure failed\n"); exit(1); }
            MT[(size_t)i * N + j] = (uint16_t)idx;
        }
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) RT[(size_t)j * N + i] = MT[(size_t)i * N + j];
    for (int i = 0; i < N; i++) {
        INV[i] = -1;
        for (int j = 0; j < N; j++) if (MT[(size_t)i * N + j] == ID) { INV[i] = j; break; }
        if (INV[i] < 0) { fprintf(stderr, "no inverse\n"); exit(1); }
    }
    /* associativity spot check */
    for (int t = 0; t < 20000; t++) {
        int i = rnd() % N, j = rnd() % N, k = rnd() % N;
        int l = MT[(size_t)MT[(size_t)i * N + j] * N + k];
        int r = MT[(size_t)i * N + MT[(size_t)j * N + k]];
        if (l != r) { fprintf(stderr, "associativity failed\n"); exit(1); }
    }
    stQ = calloc(N, sizeof(uint32_t));
    stW = calloc(N, sizeof(uint32_t));
    Ql = malloc(sizeof(int) * K * K * K * K);
}

/* fast count: W = Q.S, Q = (S S^-1)(S S^-1) */
static int evalS(const int *S) {
    static int Ap[K * K];
    int nq = 0, cnt = 0;
    stc++;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) Ap[i * K + j] = MT[(size_t)S[i] * N + INV[S[j]]];
    for (int p = 0; p < K * K; p++)
        for (int r = 0; r < K * K; r++) {
            int q = MT[(size_t)Ap[p] * N + Ap[r]];
            if (stQ[q] != stc) { stQ[q] = stc; Ql[nq++] = q; }
        }
    for (int s = 0; s < K; s++) {
        const uint16_t *col = RT + (size_t)S[s] * N; /* col[q] = q * S[s] */
        for (int t = 0; t < nq; t++) {
            int w = col[Ql[t]];
            if (stW[w] != stc) { stW[w] = stc; cnt++; }
        }
    }
    return cnt;
}

/* slow reference: all 7^5 tuples */
static int brute(const int *S) {
    static uint8_t *seen = NULL;
    if (!seen) seen = malloc(N);
    memset(seen, 0, N);
    int cnt = 0;
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            for (int c = 0; c < K; c++)
                for (int d = 0; d < K; d++)
                    for (int e = 0; e < K; e++) {
                        int x = MT[(size_t)S[a] * N + INV[S[b]]];
                        int y = MT[(size_t)x * N + S[c]];
                        int z = MT[(size_t)y * N + INV[S[d]]];
                        int w = MT[(size_t)z * N + S[e]];
                        if (!seen[w]) { seen[w] = 1; cnt++; }
                    }
    return cnt;
}

static void randS(int *S, uint8_t *inS) {
    memset(inS, 0, N);
    S[0] = ID; inS[ID] = 1;
    for (int i = 1; i < K; i++) {
        int g;
        do g = (int)(rnd() % N); while (inS[g]);
        S[i] = g; inS[g] = 1;
    }
}

static void showel(int i) {
    const El *e = &E[i];
    if (KIND == 3) printf("(%d,%d)", e->a, e->b);
    else printf("(%d,%d,%d,%d)", e->a, e->b, e->c, e->d);
    if (MZ > 1) printf("z%d", e->z);
}

int main(void) {
    const char *gs = getenv("GROUP") ? getenv("GROUP") : "sl 17";
    char kind[16] = "";
    int p = 0;
    if (sscanf(gs, "%15s %d", kind, &p) != 2) { fprintf(stderr, "bad GROUP\n"); return 1; }
    if (!strcmp(kind, "sl")) KIND = 0;
    else if (!strcmp(kind, "pgl")) KIND = 1;
    else if (!strcmp(kind, "psl")) KIND = 2;
    else if (!strcmp(kind, "agl")) KIND = 3;
    else { fprintf(stderr, "unknown kind %s\n", kind); return 1; }
    P = p;
    MZ = getenv("ZM") ? atoi(getenv("ZM")) : 1;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60.0;
    int runs = getenv("RUNS") ? atoi(getenv("RUNS")) : 3;
    rng_s = (getenv("SEED") ? strtoull(getenv("SEED"), NULL, 10) : 1ULL) * 2654435761ULL + 88172645463325252ULL;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 4.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    int check = getenv("CHECK") ? atoi(getenv("CHECK")) : 1;
    const char *outf = getenv("OUT");

    build();
    printf("GROUP %s zm=%d N=%d ID=%d\n", gs, MZ, N, ID);

    int S[K], bestS[K];
    uint8_t *inS = malloc(N);
    /* random baseline */
    double rsum = 0; int rmin = 1 << 30, rmax = 0; int NR = 400;
    for (int t = 0; t < NR; t++) {
        randS(S, inS);
        int c = evalS(S);
        rsum += c; if (c < rmin) rmin = c; if (c > rmax) rmax = c;
    }
    double rmean = rsum / NR;

    int best = -1;
    long evals = 0;
    double tstart = now();
    for (int run = 0; run < runs; run++) {
        randS(S, inS);
        int cur = evalS(S);
        evals++;
        double t0 = now(), dur = secs / runs;
        double T = T0;
        for (long it = 0;; it++) {
            if ((it & 127) == 0) {
                double el = now() - t0;
                if (el >= dur) break;
                T = T0 * pow(T1 / T0, el / dur);
            }
            int i = 1 + (int)(rnd() % (K - 1));
            int g = (int)(rnd() % N);
            if (inS[g]) continue;
            int old = S[i];
            S[i] = g;
            int nv = evalS(S);
            evals++;
            int d = nv - cur;
            if (d >= 0 || urand() < exp(d / T)) {
                inS[old] = 0; inS[g] = 1; cur = nv;
                if (cur > best) { best = cur; memcpy(bestS, S, sizeof S); }
            } else S[i] = old;
        }
    }
    double secsUsed = now() - tstart;

    if (check) {
        int bf = brute(bestS);
        if (bf != best) { fprintf(stderr, "CHECK FAILED fast=%d brute=%d\n", best, bf); return 2; }
    }
    printf("RESULT group=\"%s\" zm=%d N=%d best_cov=%d uncovered=%d best_frac=%.4f random_mean_cov=%.1f random_min=%d random_max=%d evals=%ld secs=%.1f\n",
           gs, MZ, N, best, N - best, (double)best / N, rmean, rmin, rmax, evals, secsUsed);
    printf("BESTS");
    for (int i = 0; i < K; i++) { printf(" "); showel(bestS[i]); }
    printf("\n");
    if (outf) {
        FILE *f = fopen(outf, "w");
        if (f) {
            fprintf(f, "GROUP %s zm=%d N=%d cov=%d uncov=%d\n", gs, MZ, N, best, N - best);
            for (int i = 0; i < K; i++) fprintf(f, "%d\n", bestS[i]);
            fclose(f);
        }
    }
    return 0;
}

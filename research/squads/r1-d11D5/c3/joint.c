/* joint.c: joint annealer over (nu, sigma) for the zcov covering cost on W(q) with labels in Z_a.
   cost = sum over NON-exempt opposite pairs (point pairs and line pairs) of the number of missing values in Z_a.
   Point pair {P,Q} (non-collinear) is exempt iff sigma(P), sigma(Q) are concurrent lines.
   Line pair {A,B} (non-concurrent) is exempt iff sigma^-1(A), sigma^-1(B) are collinear points.
   Moves: flip one flag label (nu), or swap sigma values of two points (sigma; only exemption changes).
   Same cost as research/d11D5/z3/zcov.c with SIGMA and IN (checked by SCORE mode).
   env: GQ (bin path), IN (nu labels, F ints), SIGMA (sigma, N ints), SEED, SECS (CPU seconds), T0, T1,
        PSIG (probability of a sigma move, default 0.5), OUT (best nu), OUTSIG (best sigma),
        SCORE=1 (evaluate IN + SIGMA only, write OUT/OUTSIG if set).
   usage: joint q a
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int q, a, N, L, Q1, F, NP, NPAIRS, nPt, nLn;
static int *pl, *lp, *colline, *concpt, *flof;
static int *pa, *pb, *pidP, *pidL, *ptPart, *lnPart;
static int *gf; static int8_t *gs; static int *occ, *ooff;
static uint8_t *val, *cnt, *mis;
static int *nu, *sig, *sinv;

/* exemption of pair k (k < NP: point pair; else line pair), depends on sigma only */
static inline int ex(int k) {
    if (k < NP) return concpt[(long)sig[pa[k]] * L + sig[pb[k]]] >= 0;
    return colline[(long)sinv[pa[k]] * N + sinv[pb[k]]] >= 0;
}
static inline int recmis(int k) { int m = 0; for (int v = 0; v < a; v++) m += (cnt[(long)k * a + v] == 0); return m; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: joint q a\n"); return 1; }
    q = atoi(argv[1]); a = atoi(argv[2]); Q1 = q + 1;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    char fnb[512];
    if (getenv("GQ")) snprintf(fnb, sizeof fnb, "%s", getenv("GQ"));
    else snprintf(fnb, sizeof fnb, "/home/user/degree-diameter/research/d11D5/z3/gq/gq_q%d.bin", q);
    FILE *f = fopen(fnb, "rb"); int32_t h[3];
    if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "no %s\n", fnb); return 1; }
    N = h[1]; L = h[2];
    if (N != L) { fprintf(stderr, "N != L\n"); return 1; }
    pl = malloc(sizeof(int) * (size_t)L * Q1);
    if (fread(pl, 4, (size_t)L * Q1, f) != (size_t)L * Q1) { fprintf(stderr, "short bin\n"); return 1; }
    fclose(f);
    F = L * Q1;
    lp = malloc(sizeof(int) * (size_t)N * Q1); flof = malloc(sizeof(int) * (size_t)N * L);
    for (long i = 0; i < (long)N * L; i++) flof[i] = -1;
    int *dg = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k];
        lp[p * Q1 + dg[p]++] = l;
        flof[(long)p * L + l] = l * Q1 + k;
    }
    colline = malloc(sizeof(int) * (size_t)N * N); for (long i = 0; i < (long)N * N; i++) colline[i] = -1;
    for (int l = 0; l < L; l++) for (int i = 0; i < Q1; i++) for (int j = 0; j < Q1; j++)
        if (i != j) colline[(long)pl[l*Q1+i] * N + pl[l*Q1+j]] = l;
    concpt = malloc(sizeof(int) * (size_t)L * L); for (long i = 0; i < (long)L * L; i++) concpt[i] = -1;
    for (int p = 0; p < N; p++) for (int i = 0; i < Q1; i++) for (int j = 0; j < Q1; j++)
        if (i != j) concpt[(long)lp[p*Q1+i] * L + lp[p*Q1+j]] = p;

    /* pairs: point pairs (non-collinear) ids [0,NP), line pairs (non-concurrent) ids [NP,NPAIRS) */
    pidP = malloc(sizeof(int) * (size_t)N * N); pidL = malloc(sizeof(int) * (size_t)L * L);
    for (long i = 0; i < (long)N * N; i++) pidP[i] = -1;
    for (long i = 0; i < (long)L * L; i++) pidL[i] = -1;
    NP = 0; for (int P = 0; P < N; P++) for (int Q = P + 1; Q < N; Q++) if (colline[(long)P*N+Q] < 0) NP++;
    int NLp = 0; for (int A = 0; A < L; A++) for (int B = A + 1; B < L; B++) if (concpt[(long)A*L+B] < 0) NLp++;
    NPAIRS = NP + NLp;
    pa = malloc(sizeof(int) * NPAIRS); pb = malloc(sizeof(int) * NPAIRS);
    int id = 0;
    for (int P = 0; P < N; P++) for (int Q = P + 1; Q < N; Q++) if (colline[(long)P*N+Q] < 0) {
        pidP[(long)P*N+Q] = pidP[(long)Q*N+P] = id; pa[id] = P; pb[id] = Q; id++; }
    for (int A = 0; A < L; A++) for (int B = A + 1; B < L; B++) if (concpt[(long)A*L+B] < 0) {
        pidL[(long)A*L+B] = pidL[(long)B*L+A] = id; pa[id] = A; pb[id] = B; id++; }

    /* partner lists (noncollinear points, nonconcurrent lines) */
    nPt = 0; for (int Q = 1; Q < N; Q++) if (colline[Q] < 0) nPt++;
    nLn = 0; for (int B = 1; B < L; B++) if (concpt[B] < 0) nLn++;
    ptPart = malloc(sizeof(int) * (size_t)N * nPt); lnPart = malloc(sizeof(int) * (size_t)L * nLn);
    for (int P = 0; P < N; P++) { int c = 0;
        for (int Q = 0; Q < N; Q++) if (Q != P && colline[(long)P*N+Q] < 0) { if (c >= nPt) { fprintf(stderr, "irregular pt\n"); return 1; } ptPart[P*nPt + c++] = Q; }
        if (c != nPt) { fprintf(stderr, "irregular pt\n"); return 1; } }
    for (int A = 0; A < L; A++) { int c = 0;
        for (int B = 0; B < L; B++) if (B != A && concpt[(long)A*L+B] < 0) { if (c >= nLn) { fprintf(stderr, "irregular ln\n"); return 1; } lnPart[A*nLn + c++] = B; }
        if (c != nLn) { fprintf(stderr, "irregular ln\n"); return 1; } }

    /* geodesics of every pair (independent of sigma): 4 flags with signs, Q1 per pair */
    long G = (long)NPAIRS * Q1;
    gf = malloc(sizeof(int) * G * 4); gs = malloc((size_t)G * 4);
    for (int k = 0; k < NP; k++) {
        int P = pa[k], Q = pb[k];
        for (int i = 0; i < Q1; i++) {
            int L1 = lp[P*Q1+i]; int R = -1;
            for (int kk = 0; kk < Q1; kk++) { int r = pl[L1*Q1+kk]; if (r != P && colline[(long)r*N+Q] >= 0) { R = r; break; } }
            if (R < 0) { fprintf(stderr, "no R\n"); return 1; }
            int L2 = colline[(long)R*N+Q];
            long g = (long)k * Q1 + i;
            gf[g*4+0] = flof[(long)P*L+L1]; gf[g*4+1] = flof[(long)R*L+L1];
            gf[g*4+2] = flof[(long)R*L+L2]; gf[g*4+3] = flof[(long)Q*L+L2];
            gs[g*4+0] = 1; gs[g*4+1] = -1; gs[g*4+2] = 1; gs[g*4+3] = -1;
        }
    }
    for (int k = NP; k < NPAIRS; k++) {
        int A = pa[k], B = pb[k];
        for (int i = 0; i < Q1; i++) {
            int P1 = pl[A*Q1+i]; int K = -1;
            for (int kk = 0; kk < Q1; kk++) { int l = lp[P1*Q1+kk]; if (l != A && concpt[(long)l*L+B] >= 0) { K = l; break; } }
            if (K < 0) { fprintf(stderr, "no K\n"); return 1; }
            int P2 = concpt[(long)K*L+B];
            long g = (long)k * Q1 + i;
            gf[g*4+0] = flof[(long)P1*L+A]; gf[g*4+1] = flof[(long)P1*L+K];
            gf[g*4+2] = flof[(long)P2*L+K]; gf[g*4+3] = flof[(long)P2*L+B];
            gs[g*4+0] = -1; gs[g*4+1] = 1; gs[g*4+2] = -1; gs[g*4+3] = 1;
        }
    }
    /* flag -> occurrences (entry e = g*4+slot) */
    int *co = calloc(F, sizeof(int));
    for (long e = 0; e < G * 4; e++) co[gf[e]]++;
    ooff = malloc(sizeof(int) * (F + 1)); ooff[0] = 0;
    int maxocc = 0;
    for (int i = 0; i < F; i++) { ooff[i+1] = ooff[i] + co[i]; if (co[i] > maxocc) maxocc = co[i]; }
    occ = malloc(sizeof(int) * (size_t)ooff[F]);
    memset(co, 0, sizeof(int) * F);
    for (long e = 0; e < G * 4; e++) { int fl = gf[e]; occ[ooff[fl] + co[fl]++] = (int)e; }
    free(co);

    /* state */
    nu = malloc(sizeof(int) * F); sig = malloc(sizeof(int) * N); sinv = malloc(sizeof(int) * L);
    if (getenv("IN")) {
        FILE *g2 = fopen(getenv("IN"), "r"); if (!g2) { fprintf(stderr, "no IN\n"); return 1; }
        for (int i = 0; i < F; i++) { int v; if (fscanf(g2, "%d", &v) != 1) { fprintf(stderr, "short IN\n"); return 1; } nu[i] = ((v % a) + a) % a; }
        fclose(g2);
    } else for (int i = 0; i < F; i++) nu[i] = rnd() % a;
    if (getenv("SIGMA")) {
        FILE *g2 = fopen(getenv("SIGMA"), "r"); if (!g2) { fprintf(stderr, "no SIGMA\n"); return 1; }
        for (int i = 0; i < N; i++) if (fscanf(g2, "%d", &sig[i]) != 1) { fprintf(stderr, "short SIGMA\n"); return 1; }
        fclose(g2);
    } else {
        for (int i = 0; i < N; i++) sig[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = sig[i]; sig[i] = sig[j]; sig[j] = t; }
    }
    for (int i = 0; i < L; i++) sinv[i] = -1;
    for (int i = 0; i < N; i++) { if (sig[i] < 0 || sig[i] >= L || sinv[sig[i]] >= 0) { fprintf(stderr, "SIGMA not a bijection\n"); return 1; } sinv[sig[i]] = i; }

    /* voltages and counts */
    val = malloc((size_t)G); cnt = calloc((size_t)NPAIRS * a, 1); mis = malloc(NPAIRS);
    for (long g = 0; g < G; g++) {
        int s = 0; for (int t = 0; t < 4; t++) s += gs[g*4+t] * nu[gf[g*4+t]];
        s = ((s % a) + a) % a; val[g] = (uint8_t)s; cnt[(long)(g / Q1) * a + s]++;
    }
    for (int k = 0; k < NPAIRS; k++) mis[k] = (uint8_t)recmis(k);
    long cost = 0, exP = 0, exL = 0;
    for (int k = 0; k < NPAIRS; k++) { int e = ex(k); if (k < NP) exP += e; else exL += e; if (!e) cost += mis[k]; }
    printf("JOINT W(%d) a=%d flags=%d point pairs=%d line pairs=%d exempt: pts %ld lines %ld cost=%ld\n",
           q, a, F, NP, NPAIRS - NP, exP, exL, cost);
    fflush(stdout);

    if (getenv("SCORE")) {
        if (getenv("OUT")) { FILE *g2 = fopen(getenv("OUT"), "w"); for (int i = 0; i < F; i++) fprintf(g2, "%d\n", nu[i]); fclose(g2); }
        if (getenv("OUTSIG")) { FILE *g2 = fopen(getenv("OUTSIG"), "w"); for (int i = 0; i < N; i++) fprintf(g2, "%d\n", sig[i]); fclose(g2); }
        return 0;
    }

    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    double psig = getenv("PSIG") ? atof(getenv("PSIG")) : 0.5;
    long best = cost;
    int *bestnu = malloc(sizeof(int) * F), *bestsig = malloc(sizeof(int) * N);
    memcpy(bestnu, nu, sizeof(int) * F); memcpy(bestsig, sig, sizeof(int) * N);
    int *tp = malloc(sizeof(int) * (maxocc + 1));
    clock_t t0 = clock(); long it = 0, acc_nu = 0, acc_sig = 0; double T = T0, lastp = 0;
    while (best > 0) {
        if ((it & 1023) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > secs) break;
            T = T0 * pow(T1 / T0, el / secs);
            if (el - lastp >= 15.0) { lastp = el; printf("t=%.0f it=%ld cost=%ld best=%ld T=%.3f acc_nu=%ld acc_sig=%ld\n", el, it, cost, best, T, acc_nu, acc_sig); fflush(stdout); }
        }
        it++;
        if (urand() < psig) {
            int P1 = rnd() % N, P2 = rnd() % N; if (P1 == P2) continue;
            int A1 = sig[P1], A2 = sig[P2];
            long dc = 0;
            for (int t = 0; t < nPt; t++) {
                int Q = ptPart[P1*nPt + t]; if (Q == P2) continue;
                int k = pidP[(long)P1*N+Q]; int m = mis[k]; if (!m) continue;
                int ox = concpt[(long)A1*L + sig[Q]] >= 0, nx = concpt[(long)A2*L + sig[Q]] >= 0;
                dc += m * ((!nx) - (!ox));
            }
            for (int t = 0; t < nPt; t++) {
                int Q = ptPart[P2*nPt + t]; if (Q == P1) continue;
                int k = pidP[(long)P2*N+Q]; int m = mis[k]; if (!m) continue;
                int ox = concpt[(long)A2*L + sig[Q]] >= 0, nx = concpt[(long)A1*L + sig[Q]] >= 0;
                dc += m * ((!nx) - (!ox));
            }
            for (int t = 0; t < nLn; t++) {
                int B = lnPart[A1*nLn + t]; if (B == A2) continue;
                int k = pidL[(long)A1*L+B]; int m = mis[k]; if (!m) continue;
                int ox = colline[(long)P1*N + sinv[B]] >= 0, nx = colline[(long)P2*N + sinv[B]] >= 0;
                dc += m * ((!nx) - (!ox));
            }
            for (int t = 0; t < nLn; t++) {
                int B = lnPart[A2*nLn + t]; if (B == A1) continue;
                int k = pidL[(long)A2*L+B]; int m = mis[k]; if (!m) continue;
                int ox = colline[(long)P2*N + sinv[B]] >= 0, nx = colline[(long)P1*N + sinv[B]] >= 0;
                dc += m * ((!nx) - (!ox));
            }
            if (dc <= 0 || urand() < exp(-dc / T)) {
                sig[P1] = A2; sig[P2] = A1; sinv[A1] = P2; sinv[A2] = P1; cost += dc; acc_sig++;
            }
        } else {
            int fl = rnd() % F; int d = 1 + rnd() % (a - 1);
            long dc = 0; int n = 0;
            for (int j = ooff[fl]; j < ooff[fl+1]; j++) {
                int e = occ[j]; long g = e >> 2; int sg = gs[e]; int k = (int)(g / Q1);
                int ov = val[g]; int nv = ((ov + sg * d) % a + a) % a;
                int m0 = mis[k];
                cnt[(long)k*a+ov]--; cnt[(long)k*a+nv]++;
                int m1 = recmis(k); mis[k] = (uint8_t)m1;
                if (!ex(k)) dc += m1 - m0;
                val[g] = (uint8_t)nv; tp[n++] = j;
            }
            if (dc <= 0 || urand() < exp(-dc / T)) {
                nu[fl] = (nu[fl] + d) % a; cost += dc; acc_nu++;
            } else {
                for (int t = n - 1; t >= 0; t--) {
                    int e = occ[tp[t]]; long g = e >> 2; int sg = gs[e]; int k = (int)(g / Q1);
                    int nv = val[g]; int ov = ((nv - sg * d) % a + a) % a;
                    cnt[(long)k*a+nv]--; cnt[(long)k*a+ov]++; mis[k] = (uint8_t)recmis(k); val[g] = (uint8_t)ov;
                }
            }
        }
        if (cost < best) { best = cost; memcpy(bestnu, nu, sizeof(int) * F); memcpy(bestsig, sig, sizeof(int) * N); }
    }
    printf("RESULT JOINT W(%d) a=%d best=%ld cur=%ld iters=%ld acc_nu=%ld acc_sig=%ld\n", q, a, best, cost, it, acc_nu, acc_sig);
    if (getenv("OUT")) { FILE *g2 = fopen(getenv("OUT"), "w"); for (int i = 0; i < F; i++) fprintf(g2, "%d\n", bestnu[i]); fclose(g2); }
    if (getenv("OUTSIG")) { FILE *g2 = fopen(getenv("OUTSIG"), "w"); for (int i = 0; i < N; i++) fprintf(g2, "%d\n", bestsig[i]); fclose(g2); }
    return 0;
}

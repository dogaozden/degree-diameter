/* Self-dual Haar search: S = {e} + nfix fixed psi-points + m psi-2-orbits, |S| = 17, psi(x) = beta(x)^-1,
   beta(i,j) = (u i, v j) on Z_n : Z_k with y x y^-1 = x^r. Cost = |G \ X X|, X = S^-1 S.
   Usage: tabu n k r u v nfix seed secs NB STALL outfile */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <sys/time.h>
#define KS 17
static double wall(void){ struct timeval tv; gettimeofday(&tv,0); return tv.tv_sec+1e-6*tv.tv_usec; }
static int n, k, N, r, u, v;
static int *rp, *rinvp, *I, *J, *invt, *stX, *stZ, *ost;
static int curX = 0, curZ = 0;
static int Xu[KS*KS + 4];
static inline int mul(int g, int h) {
    int i = I[g], j = J[g], a = I[h], b = J[h];
    int ii = (i + rp[j] * a) % n;
    int jj = (j + b) % k;
    return ii * k + jj;
}
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int cost(const int *S) {
    curX++; int nX = 0;
    for (int a = 0; a < KS; a++) { int ia = invt[S[a]];
        for (int b = 0; b < KS; b++) { int x = mul(ia, S[b]);
            if (stX[x] != curX) { stX[x] = curX; Xu[nX++] = x; } } }
    curZ++; int cov = 0;
    for (int p = 0; p < nX; p++) for (int q = 0; q < nX; q++) {
        int z = mul(Xu[p], Xu[q]);
        if (stZ[z] != curZ) { stZ[z] = curZ; cov++; } }
    return N - cov;
}
int main(int argc, char **argv) {
    if (argc < 12) { fprintf(stderr, "usage\n"); return 1; }
    n = atoi(argv[1]); k = atoi(argv[2]); r = atoi(argv[3]); u = atoi(argv[4]); v = atoi(argv[5]);
    int nfix = atoi(argv[6]); uint64_t seed = strtoull(argv[7], 0, 10); double secs = atof(argv[8]);
    int NB = atoi(argv[9]); long STALL = atol(argv[10]); const char *outf = argv[11];
    N = n * k; rs ^= seed * 0x9E3779B97F4A7C15ULL + 1; for (int i = 0; i < 10; i++) rnd();
    rp = malloc(k * sizeof(int)); rinvp = malloc(k * sizeof(int));
    int rinv = 1; { /* r^-1 mod n */ for (int t = 1; t < n; t++) if ((long)r * t % n == 1) { rinv = t; break; } }
    for (int j = 0; j < k; j++) { long p = 1, q = 1; for (int t = 0; t < j; t++) { p = p * r % n; q = q * rinv % n; } rp[j] = (int)p; rinvp[j] = (int)q; }
    I = malloc(N * sizeof(int)); J = malloc(N * sizeof(int)); invt = malloc(N * sizeof(int));
    stX = calloc(N, sizeof(int)); stZ = calloc(N, sizeof(int)); ost = calloc(N, sizeof(int));
    for (int g = 0; g < N; g++) { I[g] = g / k; J[g] = g % k; }
    for (int g = 0; g < N; g++) { int i = I[g], j = J[g];
        int b = (k - j) % k; long a = ((long)(n - i) % n) * rinvp[j] % n; invt[g] = (int)(a * k + b); }
    /* beta, psi = beta^-1 */
    int *psi = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { int i = I[g], j = J[g];
        int bg = (int)(((long)u * i % n) * k + ((long)v * j % k)); psi[g] = invt[bg]; }
    /* sanity: psi involution, psi(psi(g)) = g */
    for (int g = 0; g < N; g++) if (psi[psi[g]] != g) { printf("BADPSI\n"); return 2; }
    /* orbits: fixed points (not e) and pairs */
    int *F = malloc(N * sizeof(int)), *P1 = malloc(N * sizeof(int)), *P2 = malloc(N * sizeof(int));
    int nF = 0, nP = 0; char *seen = calloc(N, 1); seen[0] = 1;
    for (int g = 1; g < N; g++) { if (seen[g]) continue; seen[g] = 1;
        if (psi[g] == g) F[nF++] = g; else { seen[psi[g]] = 1; P1[nP] = g; P2[nP] = psi[g]; nP++; } }
    int m = (KS - 1 - nfix) / 2;
    if (nfix > nF || nP < m) { printf("RESULT group n=%d k=%d r=%d u=%d v=%d N=%d nfix=%d SKIP nF=%d nP=%d\n", n, k, r, u, v, N, nfix, nF, nP); return 0; }
    if (nfix + 2 * m != KS - 1) { printf("bad nfix\n"); return 3; }
    /* state: slots 0..nfix-1 fixed orbit ids (into F), nfix..nfix+m-1 pair ids (into P) */
    int ns = nfix + m;
    int *slot = malloc((ns + 1) * sizeof(int));
    char *inF = calloc(nF + 1, 1), *inP = calloc(nP + 1, 1);
    long *tabu = calloc(nF + nP + 1, sizeof(long));
    int *S = malloc(KS * sizeof(int)), *S2 = malloc(KS * sizeof(int));
    int *best_slot = malloc((ns + 1) * sizeof(int));
    /* id space: fixed id f -> 0..nF-1, pair id p -> nF + p */
    for (int t = 0; t < ns; t++) {
        int id;
        if (t < nfix) { do { id = rnd() % nF; } while (inF[id]); inF[id] = 1; slot[t] = id; }
        else { do { id = rnd() % nP; } while (inP[id]); inP[id] = 1; slot[t] = nF + id; }
    }
    /* build S from slots: e, fixed, pairs (1 + nfix + 2m = 17) */
    #define MKS(SS, sl) do { int q_ = 0; SS[q_++] = 0; for (int t_ = 0; t_ < ns; t_++) { int id_ = (sl)[t_]; \
        if (id_ < nF) SS[q_++] = F[id_]; else { SS[q_++] = P1[id_ - nF]; SS[q_++] = P2[id_ - nF]; } } } while (0)
    MKS(S, slot);
    long cur = cost(S), best = cur; long it = 0, stall = 0, restarts = 0;
    memcpy(best_slot, slot, (ns) * sizeof(int));
    double t0 = wall();
    int found = 0;
    while (1) {
        it++;
        if ((it & 15) == 0 && wall() - t0 > secs) break;
        long bc = -1; int bt = -1, bid = -1, bold = -1;
        for (int c = 0; c < NB; c++) {
            int t = rnd() % ns; int old = slot[t];
            int id;
            if (t < nfix) { do { id = rnd() % nF; } while (inF[id]); id = id; }
            else { do { id = nF + rnd() % nP; } while (inP[id - nF]); }
            /* id is a new orbit id (fixed: 0..nF-1 ; pair: nF + p) */
            int idn = (t < nfix) ? id : id;
            int oldid = old;
            int key_new = idn;
            /* tabu check by id */
            slot[t] = idn; MKS(S2, slot); long cc = cost(S2); slot[t] = oldid;
            int is_tabu = tabu[key_new] > it;
            if (is_tabu && !(cc < best)) continue;
            if (cc < bc || bc < 0 || (cc == bc && (rnd() & 1))) { bc = cc; bt = t; bid = idn; bold = oldid; }
        }
        if (bt < 0) continue;
        /* apply move */
        if (bold < nF) inF[bold] = 0; else inP[bold - nF] = 0;
        if (bid < nF) inF[bid] = 1; else inP[bid - nF] = 1;
        slot[bt] = bid; cur = bc;
        tabu[bold] = it + 7 + (long)(rnd() % 10);
        if (cur < best) { best = cur; memcpy(best_slot, slot, ns * sizeof(int)); stall = 0;
            fprintf(stderr, "it %ld t %.1f best %ld\n", it, wall() - t0, best); }
        else stall++;
        if (cur == 0) { found = 1; break; }
        if (stall > STALL) { /* restart from random */
            restarts++; stall = 0;
            memset(inF, 0, nF + 1); memset(inP, 0, nP + 1);
            for (int t = 0; t < ns; t++) { int id;
                if (t < nfix) { do { id = rnd() % nF; } while (inF[id]); inF[id] = 1; slot[t] = id; }
                else { do { id = rnd() % nP; } while (inP[id]); inP[id] = 1; slot[t] = nF + id; } }
            MKS(S, slot); cur = cost(S);
        }
    }
    /* report */
    memcpy(slot, best_slot, ns * sizeof(int));
    MKS(S, slot);
    int c_final = cost(S);
    printf("RESULT group n=%d k=%d r=%d u=%d v=%d N=%d nfix=%d best_cost=%ld check=%d iters=%ld restarts=%ld found=%d\n",
           n, k, r, u, v, N, nfix, best, c_final, it, restarts, found);
    if (best == 0) {
        FILE *f = fopen(outf, "w");
        fprintf(f, "%d %d %d %d %d\n", n, k, r, u, v);
        for (int a = 0; a < KS; a++) fprintf(f, "%d %d\n", I[S[a]], J[S[a]]);
        fclose(f);
    }
    return 0;
}

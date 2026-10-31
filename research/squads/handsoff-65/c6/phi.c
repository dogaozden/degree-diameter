/* phi.c (worker c6): twisted Haar-type graphs with an automorphism twist, symmetric evaluation.
 * Graph on A = {a_x}, B = {b_y}, x,y in G (|G| = m): edges a_x ~ b_{x s_i} (i = 0..4, translations S) and
 * a_x ~ b_{phi(x) t} (one twisted matching; phi an automorphism of G from an AUT file, t in G).
 * K = Fix(phi) acts on the graph by left multiplication (k a_x = a_{kx}, k b_y = b_{ky}), freely on both sides.
 * Cost = unordered pairs at distance > 5, computed exactly from K-orbit representatives:
 *   bad = |K| * (2*nr*n - sum_v popcount(R[v])) / 2, where R[v] = set of representative sources reaching v in <= 5 steps.
 * usage: phi TABLE AUTFILE SECS SEED OUTPREFIX [T0=..] [T1=..] [IPC=..] [PHI=k (fixed automorphism index)] [MAXK=..]
 * AUTFILE: first number = count, then one line of m numbers per automorphism (images of elements, 0 = identity).
 * Restarts: random S, t, automorphism (among those with |K| <= MAXK); each restart runs IPC SA steps.
 * Prints "RST ..." per restart and "END ..." at the end; writes OUTPREFIX.edges when the best improves.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static int m, n, W, nsrc, nr, Kord;
static int *mul, *inv, *phi, *sig, *sigi, *srcv;
static int S[5], tt;
static int adj[2048][6];
static uint64_t *R, *Rn;
static long cntbad;
static int *pool = NULL, npool = 0;
static int scanmode = 0;
static int steepest = 0;
static inline int pick(void) { return npool ? pool[rnd() % npool] : (int)(rnd() % m); }

static void build_adj(void) {
    for (int x = 0; x < m; x++) {
        for (int i = 0; i < 5; i++) adj[x][i] = m + mul[x * m + S[i]];
        adj[x][5] = m + sig[x];
    }
    for (int y = 0; y < m; y++) {
        for (int i = 0; i < 5; i++) adj[m + y][i] = mul[y * m + inv[S[i]]];
        adj[m + y][5] = sigi[y];
    }
}

static long score(void) {
    for (int x = 0; x < m; x++) sig[x] = mul[phi[x] * m + tt];
    for (int x = 0; x < m; x++) sigi[sig[x]] = x;
    build_adj();
    memset(R, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int j = 0; j < nsrc; j++) { int v = srcv[j]; R[(size_t)v * W + (j >> 6)] |= 1ULL << (j & 63); }
    for (int k = 0; k < 5; k++) {
        memcpy(Rn, R, sizeof(uint64_t) * (size_t)n * W);
        for (int v = 0; v < n; v++) {
            uint64_t *dst = Rn + (size_t)v * W;
            for (int j = 0; j < 6; j++) {
                const uint64_t *src = R + (size_t)adj[v][j] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = R; R = Rn; Rn = t;
    }
    long pop = 0;
    for (int v = 0; v < n; v++) for (int w = 0; w < W; w++) pop += __builtin_popcountll(R[(size_t)v * W + w]);
    long tot = (long)nsrc * n - pop;           /* sum over sources of unreached vertices */
    return (long)Kord * tot / 2;
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d\n", n);
    for (int x = 0; x < m; x++) {
        for (int i = 0; i < 5; i++) fprintf(f, "%d %d\n", x, m + mul[x * m + S[i]]);
        fprintf(f, "%d %d\n", x, m + mul[phi[x] * m + tt]);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: phi TABLE AUTFILE SECS SEED OUTPREFIX [T0= T1= IPC= PHI= MAXK=]\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) return 2;
    if (fscanf(f, "%d", &m) != 1) return 2;
    mul = malloc(sizeof(int) * m * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 2;
    fclose(f);
    inv = malloc(sizeof(int) * m);
    for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) if (mul[g * m + h] == 0) inv[g] = h;
    n = 2 * m;
    f = fopen(argv[2], "r");
    if (!f) return 2;
    int na; if (fscanf(f, "%d", &na) != 1) return 2;
    int *AUT = malloc(sizeof(int) * (size_t)na * m);
    for (int a = 0; a < na; a++) for (int x = 0; x < m; x++) if (fscanf(f, "%d", &AUT[(size_t)a * m + x]) != 1) return 2;
    fclose(f);
    double secs = atof(argv[3]);
    rs = 88172645463325252ULL ^ (uint64_t)strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *outp = argv[5];
    double T0 = 20, T1 = 1; long ipc = 200000; int fixphi = -1; int maxk = 1 << 30;
    for (int a = 6; a < argc; a++) {
        if (!strncmp(argv[a], "T0=", 3)) T0 = atof(argv[a] + 3);
        else if (!strncmp(argv[a], "T1=", 3)) T1 = atof(argv[a] + 3);
        else if (!strncmp(argv[a], "IPC=", 4)) ipc = atol(argv[a] + 4);
        else if (!strncmp(argv[a], "PHI=", 4)) fixphi = atoi(argv[a] + 4);
        else if (!strncmp(argv[a], "MAXK=", 5)) maxk = atoi(argv[a] + 5);
        else if (!strcmp(argv[a], "SCAN=1")) scanmode = 1;
        else if (!strcmp(argv[a], "STEEP=1")) steepest = 1;
        else if (!strncmp(argv[a], "S=", 2)) { char buf[256]; strncpy(buf, argv[a] + 2, 255); buf[255] = 0; int i = 0; for (char *q = strtok(buf, ","); q && i < 5; q = strtok(NULL, ",")) S[i++] = atoi(q); }
        else if (!strncmp(argv[a], "POOL=", 5)) {
            FILE *pf = fopen(argv[a] + 5, "r"); if (!pf) return 2;
            pool = malloc(sizeof(int) * m); int v;
            while (fscanf(pf, "%d", &v) == 1) if (npool < m) pool[npool++] = v;
            fclose(pf);
        }
    }
    W = 0; phi = malloc(sizeof(int) * m); sig = malloc(sizeof(int) * m); sigi = malloc(sizeof(int) * m);
    srcv = malloc(sizeof(int) * 2 * m);
    /* precompute K-orbit reps per automorphism: done on demand */
    char **seen = NULL; (void)seen;
    int *orb = malloc(sizeof(int) * m);
    int *fix = malloc(sizeof(int) * m);
    char ep[512]; snprintf(ep, sizeof ep, "%s.edges", outp);
    char logp[512]; snprintf(logp, sizeof logp, "%s.log", outp);
    FILE *lg = fopen(logp, "a");
    long best = -1; int bestS[5], bestt = 0, bestphi = -1;
    int *bestphiarr = malloc(sizeof(int) * m);
    double c0 = wall(); long restarts = 0;
    int *orb_dummy = 0; (void)orb_dummy;
    int *R0 = NULL; (void)R0;
    int Rcap = 0;

    if (scanmode) {
        /* exhaustive: fixed S (given), every automorphism in AUT and every t in G */
        long gbest = -1; int ga = -1, gt = -1;
        for (int a = 0; a < na; a++) {
            memcpy(phi, AUT + (size_t)a * m, sizeof(int) * m);
            int K = 0; for (int g = 0; g < m; g++) if (phi[g] == g) K++;
            if (K > maxk) continue;
            int *kl = malloc(sizeof(int) * K); int c = 0;
            for (int g = 0; g < m; g++) if (phi[g] == g) kl[c++] = g;
            for (int x = 0; x < m; x++) orb[x] = -1;
            nr = 0; int *reps = malloc(sizeof(int) * m);
            for (int x = 0; x < m; x++) if (orb[x] < 0) { reps[nr] = x; for (int q = 0; q < K; q++) orb[mul[kl[q] * m + x]] = nr; nr++; }
            nsrc = 2 * nr; Kord = K;
            for (int j = 0; j < nr; j++) { srcv[j] = reps[j]; srcv[nr + j] = m + reps[j]; }
            free(reps); free(kl);
            W = (nsrc + 63) / 64;
            if (Rcap < n * W) { free(R); free(Rn); R = malloc(sizeof(uint64_t) * (size_t)n * W); Rn = malloc(sizeof(uint64_t) * (size_t)n * W); Rcap = n * W; }
            for (int t = 0; t < m; t++) {
                tt = t;
                long c2 = score();
                if (gbest < 0 || c2 < gbest) { gbest = c2; ga = a; gt = t; printf("SCAN a=%d K=%d t=%d bad=%ld\n", a, K, t, c2); fflush(stdout); }
            }
        }
        printf("SCANEND best=%ld a=%d t=%d S=%d,%d,%d,%d,%d\n", gbest, ga, gt, S[0], S[1], S[2], S[3], S[4]);
        if (gbest >= 0 && ga >= 0) {
            memcpy(phi, AUT + (size_t)ga * m, sizeof(int) * m); tt = gt; write_edges(ep);
        }
        return 0;
    }

    while (wall() - c0 < secs) {
        int a = fixphi >= 0 ? fixphi : (int)(rnd() % na);
        memcpy(phi, AUT + (size_t)a * m, sizeof(int) * m);
        /* K = Fix(phi), orbits of left multiplication by K */
        int K = 0;
        for (int g = 0; g < m; g++) { fix[g] = (phi[g] == g); K += fix[g]; }
        if (K > maxk) { if (fixphi >= 0) { fprintf(stderr, "phi too large\n"); return 2; } continue; }
        Kord = K;
        int *kl = malloc(sizeof(int) * K); int c = 0;
        for (int g = 0; g < m; g++) if (fix[g]) kl[c++] = g;
        for (int x = 0; x < m; x++) orb[x] = -1;
        nr = 0;
        int *reps = malloc(sizeof(int) * m);
        for (int x = 0; x < m; x++) if (orb[x] < 0) {
            reps[nr] = x;
            for (int q = 0; q < K; q++) orb[mul[kl[q] * m + x]] = nr;
            nr++;
        }
        nsrc = 2 * nr;
        for (int j = 0; j < nr; j++) { srcv[j] = reps[j]; srcv[nr + j] = m + reps[j]; }
        free(reps); free(kl);
        W = (nsrc + 63) / 64;
        if (Rcap < n * W) {
            free(R); free(Rn);
            R = malloc(sizeof(uint64_t) * (size_t)n * W); Rn = malloc(sizeof(uint64_t) * (size_t)n * W);
            Rcap = n * W;
        }
        /* random start */
        for (int i = 0; i < 5; i++) S[i] = pick();
        tt = pick();
        long cur = score(), rbest = cur;
        int rS[5]; int rt = tt; memcpy(rS, S, sizeof S);
        double T = T0;
        if (steepest) {
            /* steepest descent with tabu over the 6 variables (S_0..S_4, t), all values in G */
            long tabu_until[6] = {0,0,0,0,0,0};
            long stepn = 0;
            for (stepn = 1; stepn <= ipc; stepn++) {
                long bc = -1; int bv = -1, bval = -1;
                for (int v = 0; v < 6; v++) {
                    int oldv = v < 5 ? S[v] : tt;
                    for (int g = 0; g < m; g++) {
                        if (g == oldv) continue;
                        if (v < 5) S[v] = g; else tt = g;
                        long c2 = score();
                        int tb = tabu_until[v] > stepn;
                        if ((!tb || c2 < rbest) && (bc < 0 || c2 < bc)) { bc = c2; bv = v; bval = g; }
                    }
                    if (v < 5) S[v] = oldv; else tt = oldv;
                }
                if (bc < 0) break;
                if (bv < 5) S[bv] = bval; else tt = bval;
                tabu_until[bv] = stepn + 4;
                cur = bc;
                if (cur < rbest) { rbest = cur; memcpy(rS, S, sizeof S); rt = tt; }
                if (rbest == 0) break;
            }
        }
        for (long it = 0; !steepest && it < ipc; it++) {
            T = T0 * pow(T1 / T0, (double)it / (double)ipc);
            int old_i = -1, old_v = 0, old_t = tt;
            if (rnd() % 6 == 0) { old_t = tt; tt = pick(); }
            else { old_i = rnd() % 5; old_v = S[old_i]; S[old_i] = pick(); }
            long nc = score();
            long d = nc - cur;
            if (d <= 0 || urand() < exp(-d / T)) {
                cur = nc;
                if (cur < rbest) { rbest = cur; memcpy(rS, S, sizeof S); rt = tt; }
            } else {
                if (old_i >= 0) S[old_i] = old_v; else tt = old_t;
            }
            if (rbest == 0) break;
        }
        restarts++;
        printf("RST phi=%d K=%d nsrc=%d best=%ld S=%d,%d,%d,%d,%d t=%d\n", a, K, nsrc, rbest, rS[0], rS[1], rS[2], rS[3], rS[4], rt);
        fflush(stdout);
        if (best < 0 || rbest < best) {
            best = rbest; memcpy(bestS, rS, sizeof rS); bestt = rt; bestphi = a; memcpy(bestphiarr, phi, sizeof(int) * m);
            memcpy(S, bestS, sizeof S); tt = bestt; memcpy(phi, bestphiarr, sizeof(int) * m);
            { for (int x = 0; x < m; x++) sig[x] = mul[phi[x] * m + tt]; }
            write_edges(ep);
            if (lg) { fprintf(lg, "n=%d best=%ld phi=%d K=%d S=%d,%d,%d,%d,%d t=%d\n", n, best, a, K, bestS[0], bestS[1], bestS[2], bestS[3], bestS[4], bestt); fflush(lg); }
            if (best == 0) { printf("FOUND n=%d\n", n); break; }
        }
    }
    printf("END m=%d n=%d best=%ld restarts=%ld phi=%d S=%d,%d,%d,%d,%d t=%d\n", m, n, best, restarts, bestphi,
           bestS[0], bestS[1], bestS[2], bestS[3], bestS[4], bestt);
    if (lg) fclose(lg);
    return 0;
}

/* b10: Haar graphs H(G,S) on G = SL(2,8) x D_P (dihedral of order 2P, P prime).
 * alpha = tau x beta on G, tau = field automorphism x -> x^2 of GF(8) (MODE 0) or
 * conjugation by an order-3 element c of SL(2,8) (MODE 1); beta(a,j) = (U a, j) with U^3 = 1 mod P.
 * Vertices (g,A) = index g, (g,B) = index N+g. Edges (g,A) ~ (s g,B) for s in S.
 * Cost = number of vertices not within distance 12 of (e,A) (plus same from (e,B)); 0 means diameter <= 12.
 * Usage: haar_sl8d P U MODE D e|r SECS SEED START END OUTPREFIX
 *   e: exhaustive over orbit representatives [START,END) (D = 4 only);  r: random sampling for SECS seconds.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define NSL 504
static int fmul[8][8];
static int mA[NSL][4];
static int invSLa[NSL];
static int sigSL[NSL];
static int tauSL[NSL];
static uint16_t mulSL[NSL][NSL];
static int keyidx[4096];
static int P, U, D, MODE, M2, N, NV, EID, IDSL, cSL, cinvSL;
static int S[8], Sinv[8], nS;
static uint8_t *dist;
static int32_t *qu;
static const int L = 12;

static void init_gf(void)
{
    for (int a = 0; a < 8; a++)
        for (int b = 0; b < 8; b++) {
            int r = 0, x = a;
            for (int i = 0; i < 3; i++) {
                if ((b >> i) & 1) r ^= x;
                x <<= 1;
                if (x & 8) x ^= 0xB; /* modulus x^3 + x + 1 */
            }
            fmul[a][b] = r;
        }
}

static void init_sl(void)
{
    int n = 0;
    for (int a = 0; a < 8; a++)
        for (int b = 0; b < 8; b++)
            for (int c = 0; c < 8; c++)
                for (int d = 0; d < 8; d++)
                    if ((fmul[a][d] ^ fmul[b][c]) == 1) {
                        mA[n][0] = a; mA[n][1] = b; mA[n][2] = c; mA[n][3] = d;
                        keyidx[(a << 9) | (b << 6) | (c << 3) | d] = n;
                        n++;
                    }
    if (n != NSL) { fprintf(stderr, "bad |SL(2,8)| = %d\n", n); exit(1); }
    for (int i = 0; i < NSL; i++)
        for (int j = 0; j < NSL; j++) {
            int a = mA[i][0], b = mA[i][1], c = mA[i][2], d = mA[i][3];
            int e = mA[j][0], f = mA[j][1], g = mA[j][2], h = mA[j][3];
            int r00 = fmul[a][e] ^ fmul[b][g], r01 = fmul[a][f] ^ fmul[b][h];
            int r10 = fmul[c][e] ^ fmul[d][g], r11 = fmul[c][f] ^ fmul[d][h];
            mulSL[i][j] = keyidx[(r00 << 9) | (r01 << 6) | (r10 << 3) | r11];
        }
    IDSL = keyidx[(1 << 9) | (0 << 6) | (0 << 3) | 1];
    for (int i = 0; i < NSL; i++) {
        int a = mA[i][0], b = mA[i][1], c = mA[i][2], d = mA[i][3];
        invSLa[i] = keyidx[(d << 9) | (b << 6) | (c << 3) | a];
        if (mulSL[i][invSLa[i]] != IDSL) { fprintf(stderr, "inverse fail\n"); exit(1); }
        sigSL[i] = keyidx[(fmul[a][a] << 9) | (fmul[b][b] << 6) | (fmul[c][c] << 3) | fmul[d][d]];
    }
    /* order-3 element c for conjugation mode */
    cSL = -1;
    for (int i = 0; i < NSL && cSL < 0; i++)
        if (i != IDSL && mulSL[mulSL[i][i]][i] == IDSL) { cSL = i; cinvSL = mulSL[i][i]; }
    for (int i = 0; i < NSL; i++) {
        if (MODE == 0) tauSL[i] = sigSL[i];
        else tauSL[i] = mulSL[mulSL[cSL][i]][cinvSL];
    }
}

static inline int mulD(int x, int y)
{
    int a = x >> 1, j = x & 1, b = y >> 1, k = y & 1;
    int r = j ? (a + P - b) % P : (a + b) % P;
    return r * 2 + (j ^ k);
}
static inline int invD(int x)
{
    int a = x >> 1, j = x & 1;
    return j ? x : ((P - a) % P) * 2;
}
static inline int mulG(int g, int h)
{
    int gi = g / M2, gx = g - gi * M2, hi = h / M2, hx = h - hi * M2;
    return mulSL[gi][hi] * M2 + mulD(gx, hx);
}
static inline int invG(int g)
{
    int gi = g / M2, gx = g - gi * M2;
    return invSLa[gi] * M2 + invD(gx);
}
static inline int alphaG(int g)
{
    int gi = g / M2, gx = g - gi * M2;
    int a = gx >> 1, j = gx & 1;
    int bx = ((U * a) % P) * 2 + j;
    return tauSL[gi] * M2 + bx;
}

static void setS(const int *g, int n)
{
    nS = n;
    for (int t = 0; t < n; t++) { S[t] = g[t]; Sinv[t] = invG(g[t]); }
}

/* BFS from src to depth L; returns number of vertices at distance > L (or unreached) */
static int bfs(int src)
{
    memset(dist, 255, NV);
    int head = 0, tail = 0;
    qu[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        int v = qu[head++];
        int d = dist[v];
        if (d >= L) continue;
        if (v < N) {
            for (int t = 0; t < nS; t++) {
                int w = N + mulG(S[t], v);
                if (dist[w] == 255) { dist[w] = d + 1; qu[tail++] = w; }
            }
        } else {
            int h = v - N;
            for (int t = 0; t < nS; t++) {
                int w = mulG(Sinv[t], h);
                if (dist[w] == 255) { dist[w] = d + 1; qu[tail++] = w; }
            }
        }
    }
    return NV - tail;
}

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void)
{
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void writeSol(const char *path, const int *g, int n, int cost)
{
    FILE *f = fopen(path, "w");
    if (!f) { perror("fopen"); return; }
    fprintf(f, "# haar_sl8d solution: G = SL(2,8) x D_%d, U=%d, MODE=%d, cost=%d\n", P, U, MODE, cost);
    fprintf(f, "P %d U %d MODE %d D %d\n", P, U, MODE, n);
    for (int t = 0; t < n; t++) {
        int gi = g[t] / M2, gx = g[t] - gi * M2;
        fprintf(f, "S %d %d %d %d  %d %d\n", mA[gi][0], mA[gi][1], mA[gi][2], mA[gi][3], gx >> 1, gx & 1);
    }
    fclose(f);
}

int main(int argc, char **argv)
{
    if (argc < 11) {
        fprintf(stderr, "usage: haar_sl8d P U MODE D e|r SECS SEED START END OUTPREFIX\n");
        return 1;
    }
    P = atoi(argv[1]); U = atoi(argv[2]); MODE = atoi(argv[3]); D = atoi(argv[4]);
    char search = argv[5][0];
    double secs = atof(argv[6]);
    rs ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL;
    long start = atol(argv[8]), end = atol(argv[9]);
    const char *outp = argv[10];
    if (((U * U * U) % P) != 1 || U % P == 1) { fprintf(stderr, "U must have order 3 mod P\n"); return 1; }
    M2 = 2 * P;
    N = NSL * M2;
    NV = 2 * N;
    init_gf();
    init_sl();
    EID = IDSL * M2;
    dist = malloc(NV);
    qu = malloc((size_t)NV * sizeof(int32_t));
    int *reps = malloc((size_t)N * sizeof(int));
    int *fix = malloc((size_t)N * sizeof(int));
    int nrep = 0, nfix = 0;
    for (int g = 0; g < N; g++) {
        int a1 = alphaG(g);
        if (a1 == g) { fix[nfix++] = g; continue; }
        int a2 = alphaG(a1);
        if (g < a1 && g < a2) reps[nrep++] = g;
    }
    /* sanity: alpha has order 3 and is an automorphism (random pairs) */
    for (int t = 0; t < 2000; t++) {
        int a = (int)(rnd() % N), b = (int)(rnd() % N);
        if (alphaG(alphaG(alphaG(a))) != a) { fprintf(stderr, "alpha^3 != 1\n"); return 1; }
        if (alphaG(mulG(a, b)) != mulG(alphaG(a), alphaG(b))) { fprintf(stderr, "alpha not a homomorphism\n"); return 1; }
    }
    fprintf(stderr, "N=%d |V|=%d reps=%d fixed(alpha)=%d MODE=%d P=%d U=%d\n", N, NV, nrep, nfix, MODE, P, U);
    if (nfix < 2) { fprintf(stderr, "fixed set too small\n"); }

    int hist[201];
    memset(hist, 0, sizeof hist);
    int best = 1 << 30, nfound = 0;
    long tested = 0;
    double t0 = now();

    if (search == 'e') {
        if (D != 4) { fprintf(stderr, "exhaustive mode is for D=4\n"); return 1; }
        if (end > nrep || end <= 0) end = nrep;
        for (long r = start; r < end; r++) {
            int g = reps[r];
            int a1 = alphaG(g), a2 = alphaG(a1);
            int Sg[4] = { EID, g, a1, a2 };
            setS(Sg, 4);
            int ca = bfs(EID);
            tested++;
            hist[ca > 200 ? 200 : ca]++;
            if (ca < best) { best = ca; fprintf(stderr, "  new best costA=%d at rep %ld (g=%d)\n", ca, r, g); }
            if (ca == 0) {
                int cb = bfs(N + EID);
                if (cb == 0) {
                    char path[512];
                    snprintf(path, sizeof path, "%s_%ld.txt", outp, r);
                    writeSol(path, Sg, 4, 0);
                    nfound++;
                    fprintf(stderr, "  FOUND cost-0 at rep %ld -> %s\n", r, path);
                } else {
                    fprintf(stderr, "  costA=0 but costB=%d at rep %ld\n", cb, r);
                }
            }
            if (now() - t0 > secs) { fprintf(stderr, "time limit at r=%ld\n", r); break; }
        }
    } else {
        long it = 0;
        while (now() - t0 < secs) {
            int g = reps[rnd() % (uint64_t)nrep];
            int a1 = alphaG(g), a2 = alphaG(a1);
            int Sg[5];
            int n;
            if (search == 'u') { /* baseline: unstructured random S = {e, 3 random elements} (D=4) */
                Sg[0] = EID; Sg[1] = (int)(rnd() % N); Sg[2] = (int)(rnd() % N); Sg[3] = (int)(rnd() % N);
                g = Sg[1]; n = 4;
                if (Sg[1] == EID || Sg[2] == EID || Sg[3] == EID || Sg[1] == Sg[2] || Sg[1] == Sg[3] || Sg[2] == Sg[3]) continue;
                setS(Sg, n);
                int ca = bfs(EID);
                tested++;
                hist[ca > 200 ? 200 : ca]++;
                if (ca < best) { best = ca; fprintf(stderr, "  new best costA=%d after %ld samples\n", ca, tested); }
                if (ca == 0 && bfs(N + EID) == 0) { char path[512]; snprintf(path, sizeof path, "%s_u%d.txt", outp, nfound); writeSol(path, Sg, n, 0); nfound++; }
                continue;
            }
            if (D == 4) {
                Sg[0] = EID; Sg[1] = g; Sg[2] = a1; Sg[3] = a2; n = 4;
            } else {
                int f;
                do { f = fix[rnd() % (uint64_t)nfix]; } while (f == EID);
                Sg[0] = EID; Sg[1] = f; Sg[2] = g; Sg[3] = a1; Sg[4] = a2; n = 5;
            }
            setS(Sg, n);
            int ca = bfs(EID);
            tested++;
            hist[ca > 200 ? 200 : ca]++;
            if (ca < best) { best = ca; fprintf(stderr, "  new best costA=%d after %ld samples (%.1fs)\n", ca, tested, now() - t0); }
            if (ca == 0) {
                int cb = bfs(N + EID);
                if (cb == 0) {
                    char path[512];
                    snprintf(path, sizeof path, "%s_%d.txt", outp, nfound);
                    writeSol(path, Sg, n, 0);
                    nfound++;
                    fprintf(stderr, "  FOUND cost-0 after %ld samples -> %s\n", tested, path);
                }
            }
            it++;
        }
    }
    double el = now() - t0;
    printf("RESULT P=%d U=%d MODE=%d D=%d search=%c tested=%ld found=%d best_costA=%d time=%.1fs per_bfs_ms=%.2f\n",
           P, U, MODE, D, search, tested, nfound, best, el, tested ? 1000.0 * el / tested : 0.0);
    printf("HIST");
    for (int c = 0; c <= 200; c++) if (hist[c]) printf(" %d:%d", c, hist[c]);
    printf("\n");
    return 0;
}

/* w09: Z_M-cover search. Base Haar graph H(G,S) (solved, diameter 9), cover K = G x Z_M with
 * S' = {(s, c_s)}, c_e = 0. Cost = |K \ (S'^-1 S')^4| + |K \ (S' S'^-1)^4|  (0 iff diameter <= 9).
 * Group arithmetic for G is taken from research/frontier/haar_gen3.c (included below).
 * usage: w09cover SOLFILE M MODE SECS SEED [K-random-baseline]
 *   MODE = exh   : exhaustive over c in Z_M^{d-1} (only if M^{d-1} <= 2e6), prints histogram of costs
 *   MODE = anneal: simulated annealing over c, restarts until SECS; prints best c and cost
 *   MODE = rand  : cost of random c (SECS samples), prints min/median/mean
 *   MODE = rndK  : cost of random S' in K (no cover structure), SECS samples: baseline
 */
#define main haar_gen3_main
#include "/home/user/degree-diameter/research/frontier/haar_gen3.c"
#undef main
#include <time.h>

static int wM, wd, wNG, wNK;
static int wS[MAXD], wC[MAXD], wS2[MAXD];
static int *wstamp; static int wcur = 0;
static int *wbufA, *wbufB;
static int wsizeA, wsizeB;

static inline int kmul(int u, int v) {
    int x1 = u / wM, z1 = u % wM, x2 = v / wM, z2 = v % wM;
    return gmul(x1, x2) * wM + (z1 + z2) % wM;
}
static inline int kinv(int u) { return ginv(u / wM) * wM + (wM - u % wM) % wM; }

/* Y1: {s^-1 t}, Y2: {s t^-1} over S' */
static int buildY(int *Y, int sign) {
    int n = 0; wcur++;
    for (int i = 0; i < wd; i++) for (int j = 0; j < wd; j++) {
        int a = wS2[i], b = wS2[j];
        int p = sign > 0 ? kmul(kinv(a), b) : kmul(a, kinv(b));
        if (wstamp[p] != wcur) { wstamp[p] = wcur; Y[n++] = p; }
    }
    return n;
}
/* X <- X * Y (set product), dedupe with stamps */
static int setprod(int *X, int nx, const int *Y, int ny, int *out) {
    int n = 0; wcur++;
    for (int i = 0; i < nx; i++) for (int j = 0; j < ny; j++) {
        int p = kmul(X[i], Y[j]);
        if (wstamp[p] != wcur) { wstamp[p] = wcur; out[n++] = p; }
    }
    return n;
}
/* uncovered count of Y^4 in K */
static int uncov4(const int *Y, int ny) {
    int *A = wbufA, *B = wbufB;
    int na = ny; memcpy(A, Y, sizeof(int) * ny);
    for (int j = 2; j <= 4; j++) { na = setprod(A, na, Y, ny, B); int *t = A; A = B; B = t; }
    return wNK - na;
}
static int cover_cost(void) {
    /* wC[0] = 0 enforced by caller; wS2[i] = wS[i]*M + wC[i] */
    for (int i = 0; i < wd; i++) wS2[i] = wS[i] * wM + wC[i];
    int *Y = wbufB + 0; /* reuse buffers carefully: use separate arrays */
    static int *Y1 = NULL, *Y2 = NULL;
    if (!Y1) { Y1 = malloc(sizeof(int) * 4096); Y2 = malloc(sizeof(int) * 4096); }
    (void)Y;
    int n1 = buildY(Y1, +1); int c1 = uncov4(Y1, n1);
    int n2 = buildY(Y2, -1); int c2 = uncov4(Y2, n2);
    return c1 + c2;
}
static unsigned long long wrs = 88172645463325252ULL;
static inline unsigned long long wrnd(void) { wrs ^= wrs << 13; wrs ^= wrs >> 7; wrs ^= wrs << 17; return wrs; }
static double wnow(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: w09cover SOL M MODE SECS SEED\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("sol"); return 2; }
    wM = atoi(argv[2]); const char *mode = argv[3]; double secs = atof(argv[4]); wrs ^= (unsigned long long)atoll(argv[5]) * 2654435761ULL + 1;
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    /* "d D <group tokens> n NCYC N NTOT" */
    char *tok[64]; int nt = 0; char *p = strtok(line, " \n"); while (p && nt < 64) { tok[nt++] = p; p = strtok(NULL, " \n"); }
    wd = atoi(tok[0]); int gi = 2; char *gargv[16]; int ga = 1; gargv[0] = "g";
    while (gi < nt && strcmp(tok[gi], "n")) gargv[ga++] = tok[gi++];
    ncyc = atoi(tok[gi + 1]);
    /* parse_group expects argv[a..] with a index */
    int aidx = 1; Q = parse_group(gargv, ga, &aidx);
    wNG = Q->order * ncyc; N = wNG;
    /* haar_gen3 globals */
    CHI = malloc(Q->order); memset(CHI, 1, Q->order);
    ident = Q->ident * ncyc;
    wNK = wNG * wM;
    int ng = 0; for (int i = 0; i < wd; i++) {
        if (!fgets(line, sizeof line, f)) return 2;
        wS[i] = atoi(strtok(line, " \n")); ng++;
    }
    fclose(f);
    wstamp = calloc(wNK, sizeof(int)); wbufA = malloc(sizeof(int) * wNK); wbufB = malloc(sizeof(int) * wNK);
    /* sanity: first generator is identity */
    if (wS[0] != ident) { fprintf(stderr, "warning: first generator is not identity\n"); }
    for (int i = 0; i < wd; i++) wC[i] = 0;
    int base_cost = cover_cost();   /* M = 1 uses c = 0 (valid only when M == 1) */
    fprintf(stderr, "G order %d, K order %d, d=%d, base-cover cost(c=0) = %d\n", wNG, wNK, wd, base_cost);
    double t0 = wnow();
    if (!strcmp(mode, "exh")) {
        long long tot = 1; for (int i = 1; i < wd; i++) tot *= wM;
        if (tot > 2000000) { fprintf(stderr, "too many\n"); return 2; }
        int hist[1000000 > 0 ? 4096 : 1]; (void)hist;
        int best = 1 << 30; long long cnt[64] = {0};
        for (long long code = 0; code < tot; code++) {
            long long c = code; wC[0] = 0; for (int i = 1; i < wd; i++) { wC[i] = c % wM; c /= wM; }
            int cost = cover_cost();
            if (cost < best) { best = cost; printf("best %d c=", cost); for (int i = 0; i < wd; i++) printf("%d ", wC[i]); printf("\n"); fflush(stdout); }
            if (cost < 64) cnt[cost]++;
            if (wnow() - t0 > secs) { printf("time limit after %lld of %lld\n", code, tot); break; }
        }
        printf("done best=%d; counts of cost<64:", best); for (int i = 0; i < 64; i++) if (cnt[i]) printf(" %d:%lld", i, cnt[i]); printf("\n");
    } else if (!strcmp(mode, "rand") || !strcmp(mode, "anneal")) {
        int gbest = 1 << 30; long long evals = 0; double *dummy = NULL; (void)dummy;
        int restarts = 0;
        while (wnow() - t0 < secs) {
            for (int i = 1; i < wd; i++) wC[i] = wrnd() % wM; wC[0] = 0;
            int cur = cover_cost(); evals++;
            if (!strcmp(mode, "rand")) { if (cur < gbest) gbest = cur; continue; }
            double T = 2.0; int bestc = cur; int Cb[MAXD]; memcpy(Cb, wC, sizeof wC);
            for (int step = 0; step < 3000 && wnow() - t0 < secs; step++) {
                int i = 1 + wrnd() % (wd - 1); int old = wC[i];
                wC[i] = (old + 1 + wrnd() % (wM - 1)) % wM;
                int nc = cover_cost(); evals++;
                if (nc <= cur || (double)(wrnd() % 1000000) / 1e6 < exp(-(nc - cur) / T)) { cur = nc; if (cur < bestc) { bestc = cur; memcpy(Cb, wC, sizeof wC); } }
                else wC[i] = old;
                T *= 0.998; if (T < 0.2) T = 0.2;
                if (bestc == 0) break;
            }
            restarts++;
            if (bestc < gbest) { gbest = bestc; printf("best %d c=", bestc); for (int i = 0; i < wd; i++) printf("%d ", Cb[i]); printf(" (restart %d, evals %lld)\n", restarts, evals); fflush(stdout); }
            if (gbest == 0) break;
        }
        printf("done best=%d evals=%lld restarts=%d time=%.1f\n", gbest, evals, restarts, wnow() - t0);
    } else if (!strcmp(mode, "rndK")) {
        /* random S' in K with e: baseline */
        int gbest = 1 << 30; long long evals = 0; int samples[100000]; int ns = 0;
        while (wnow() - t0 < secs && ns < 100000) {
            for (int i = 1; i < wd; i++) { int ok; do { wS2[i] = wrnd() % wNK; ok = 1; for (int j = 0; j < i; j++) if (wS2[j] == wS2[i]) ok = 0; } while (!ok); }
            wS2[0] = 0; /* identity of K is 0 * M + 0 ... ident*M */
            wS2[0] = ident * wM;
            int cost = 0; { int *Y1 = malloc(sizeof(int) * 4096), *Y2 = malloc(sizeof(int) * 4096);
              int n1 = buildY(Y1, +1); cost += uncov4(Y1, n1); int n2 = buildY(Y2, -1); cost += uncov4(Y2, n2); free(Y1); free(Y2); }
            evals++; samples[ns++] = cost; if (cost < gbest) gbest = cost;
        }
        /* median */
        for (int i = 1; i < ns; i++) { int v = samples[i], j = i - 1; while (j >= 0 && samples[j] > v) { samples[j + 1] = samples[j]; j--; } samples[j + 1] = v; }
        printf("rndK samples=%d min=%d median=%d\n", ns, samples[0], ns ? samples[ns / 2] : -1);
    }
    return 0;
}

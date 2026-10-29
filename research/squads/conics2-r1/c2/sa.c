/* SA over bijections sigma: points -> lines of H(5) maximizing #good points.
   good(x) iff sigma maps the 30 points collinear with x into the 30 lines meeting sigma(x).
   usage: sa SEED ITERS T0 T1 ALPHA INIT(-|file) OUTPREFIX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define N 3906
#define D 30
static int nb[N][D];
static unsigned char LL[(size_t)N * N];
static int sig[N];
static int stampv[N]; static int cur = 0;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int viol(int x) {
    const unsigned char *row = LL + (size_t)sig[x] * N;
    int c = 0;
    for (int k = 0; k < D; k++) c += !row[sig[nb[x][k]]];
    return c;
}
static double ALPHA;
static inline double costf(int v) { return (v > 0) + ALPHA * v; }
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage\n"); return 1; }
    uint64_t seed = strtoull(argv[1], 0, 10); long long iters = atoll(argv[2]);
    double T0 = atof(argv[3]), T1 = atof(argv[4]); ALPHA = atof(argv[5]);
    const char *init = argv[6]; const char *outp = argv[7];
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    FILE *f = fopen("nbr.bin", "rb"); if (!f || fread(nb, sizeof(int), N * D, f) != N * D) { fprintf(stderr, "nbr\n"); return 1; } fclose(f);
    f = fopen("LL.bin", "rb"); if (!f || fread(LL, 1, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "LL\n"); return 1; } fclose(f);
    if (strcmp(init, "-") == 0) {
        for (int i = 0; i < N; i++) sig[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = sig[i]; sig[i] = sig[j]; sig[j] = t; }
    } else {
        int32_t buf[N]; f = fopen(init, "rb"); if (!f || fread(buf, 4, N, f) != N) { fprintf(stderr, "init\n"); return 1; } fclose(f);
        for (int i = 0; i < N; i++) sig[i] = buf[i];
    }
    static int vv[N];
    double cost = 0; int good = 0;
    for (int x = 0; x < N; x++) { vv[x] = viol(x); cost += costf(vv[x]); good += vv[x] == 0; }
    int best = good; int S[256]; int vb[256];
    fprintf(stderr, "init good=%d cost=%.2f\n", good, cost);
    for (long long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int u = rnd() % N, v = rnd() % N; if (u == v) continue;
        cur++; int ns = 0;
        #define ADD(z) do { int _z = (z); if (stampv[_z] != cur) { stampv[_z] = cur; S[ns++] = _z; } } while (0)
        ADD(u); ADD(v);
        for (int k = 0; k < D; k++) { ADD(nb[u][k]); ADD(nb[v][k]); }
        double cb = 0; int gb = 0;
        for (int i = 0; i < ns; i++) { vb[i] = viol(S[i]); cb += costf(vb[i]); gb += vb[i] == 0; }
        int t = sig[u]; sig[u] = sig[v]; sig[v] = t;
        double ca = 0; int ga = 0;
        int va[256];
        for (int i = 0; i < ns; i++) { va[i] = viol(S[i]); ca += costf(va[i]); ga += va[i] == 0; }
        double d = ca - cb;
        if (d <= 0 || urand() < exp(-d / T)) {
            cost += d; good += ga - gb;
            for (int i = 0; i < ns; i++) vv[S[i]] = va[i];
            if (good > best) {
                best = good;
                char fn[512]; sprintf(fn, "%s_best.bin", outp);
                FILE *g = fopen(fn, "wb"); int32_t buf[N]; for (int i = 0; i < N; i++) buf[i] = sig[i]; fwrite(buf, 4, N, g); fclose(g);
                fprintf(stderr, "it %lld new best good=%d cost=%.2f\n", it, good, cost);
            }
        } else {
            t = sig[u]; sig[u] = sig[v]; sig[v] = t;
        }
        if (it % 2000000 == 0) fprintf(stderr, "it %lld T=%.4f good=%d best=%d cost=%.2f\n", it, T, good, best, cost);
    }
    /* final check of cost consistency */
    int g2 = 0; for (int x = 0; x < N; x++) g2 += viol(x) == 0;
    fprintf(stderr, "final good=%d (recount %d) best=%d\n", good, g2, best);
    char fn[512]; sprintf(fn, "%s_last.bin", outp);
    FILE *g = fopen(fn, "wb"); int32_t buf[N]; for (int i = 0; i < N; i++) buf[i] = sig[i]; fwrite(buf, 4, N, g); fclose(g);
    printf("%d\n", best);
    return 0;
}

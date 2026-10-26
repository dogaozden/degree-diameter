/* c01: annealer for Haar graphs H(G,S), |S| = 4, e in S (D = 8) with a margin objective.
 * Vertices (g,A), (g,B); edges (g,A) ~ (s g,B).  Walks are label sequences with consecutive labels distinct
 * (non-backtracking); a walk of length j <= 8 from a base point reaches its endpoint at distance j.
 * For each base point (e,A), (e,B) and each vertex x: M[x] = number of such walks of length <= 8 ending at x.
 *   uncovered U = sum over both base points and both sides of #{x : M[x] = 0}   (U = 0 iff diameter <= 8)
 *   margin Mg   = sum of #{x != base : M[x] = 1}                                  (elements covered by one walk)
 * Energy = U + W * Mg.  Simulated annealing over S (4 distinct labels, s_0 = e) with one replacement per move.
 * Usage: margin TABLE.bin SECONDS SEED W T0 T1 COOL OUTPREFIX
 *        margin TABLE.bin eval s1 s2 s3           (prints U and Mg for S = {e, s1, s2, s3})
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define NL 4
#define LMAX 8

static int N;
static uint16_t *T;
static int *INV;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int *PL, *PLI;
static uint32_t *cur, *nxt, *tot, *ntot, *Ms, *Mo;

static void build_perm(const int *s) {
    for (int l = 0; l < NL; l++) {
        int a = s[l], ai = INV[a];
        for (int v = 0; v < N; v++) {
            PL[l * N + v] = T[(size_t)a * N + v];       /* a * v */
            PLI[l * N + v] = T[(size_t)ai * N + v];     /* a^-1 * v */
        }
    }
}

/* walks from the base point on side st (0 = A, 1 = B); Ms = walks of even length (base side), Mo = odd */
static void walk(int st) {
    memset(cur, 0, sizeof(uint32_t) * NL * N);
    memset(tot, 0, sizeof(uint32_t) * N);
    memset(Ms, 0, sizeof(uint32_t) * N);
    memset(Mo, 0, sizeof(uint32_t) * N);
    tot[0] = 1; Ms[0] = 1;
    for (int j = 1; j <= LMAX; j++) {
        int side_from = (st + j - 1) & 1;
        const int *P = side_from == 0 ? PL : PLI;
        memset(nxt, 0, sizeof(uint32_t) * NL * N);
        for (int l = 0; l < NL; l++) {
            uint32_t *nl = nxt + l * N, *cl = cur + l * N;
            const int *Pl = P + l * N;
            for (int v = 0; v < N; v++) nl[Pl[v]] += tot[v] - cl[v];   /* sum of walks whose last label != l */
        }
        memset(ntot, 0, sizeof(uint32_t) * N);
        for (int l = 0; l < NL; l++) { uint32_t *nl = nxt + l * N; for (int u = 0; u < N; u++) ntot[u] += nl[u]; }
        uint32_t *M = (j % 2 == 0) ? Ms : Mo;
        for (int u = 0; u < N; u++) M[u] += ntot[u];
        uint32_t *t;
        t = cur; cur = nxt; nxt = t;
        t = tot; tot = ntot; ntot = t;
    }
}

static void evaluate(const int *s, long long *U, long long *Mg) {
    build_perm(s);
    long long u = 0, m = 0;
    for (int st = 0; st < 2; st++) {
        walk(st);
        for (int x = 0; x < N; x++) {
            if (Ms[x] == 0) u++; else if (Ms[x] == 1 && x) m++;
            if (Mo[x] == 0) u++; else if (Mo[x] == 1) m++;
        }
    }
    *U = u; *Mg = m;
}

static void write_edges(const int *s, const char *path) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d\n", 2 * N);
    for (int l = 0; l < NL; l++)
        for (int g = 0; g < N; g++) fprintf(f, "%d %d\n", g, N + T[(size_t)s[l] * N + g]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see source\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("table"); return 1; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 1; N = n32;
    T = malloc(sizeof(uint16_t) * (size_t)N * N);
    if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 1;
    fclose(f);
    INV = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { INV[g] = h; break; }
    PL = malloc(sizeof(int) * NL * N); PLI = malloc(sizeof(int) * NL * N);
    cur = malloc(4 * NL * N); nxt = malloc(4 * NL * N); tot = malloc(4 * N); ntot = malloc(4 * N);
    Ms = malloc(4 * N); Mo = malloc(4 * N);

    if (strcmp(argv[2], "eval") == 0) {
        int s[NL] = {0, atoi(argv[3]), atoi(argv[4]), atoi(argv[5])};
        long long U, Mg; evaluate(s, &U, &Mg);
        printf("eval U=%lld margin=%lld\n", U, Mg);
        return 0;
    }

    double secs = atof(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    double W = atof(argv[4]), T0 = atof(argv[5]), T1 = atof(argv[6]), COOL = atof(argv[7]);
    const char *out = argv[8];

    int s[NL] = {0, 0, 0, 0};
    for (int i = 1; i < NL; i++) {
        int x; int ok;
        do { x = 1 + (int)(rnd() % (N - 1)); ok = 1; for (int k = 0; k < i; k++) if (s[k] == x) ok = 0; } while (!ok);
        s[i] = x;
    }
    long long U, Mg; evaluate(s, &U, &Mg);
    double E = U + W * Mg;
    long long bestU = U, bestMg = Mg; int bestS[NL]; memcpy(bestS, s, sizeof s);
    long long evals = 1, acc = 0;
    double t0 = now(), Tc = T0;
    int iter = 0;
    while (bestU > 0) {
        if ((iter++ & 63) == 0) {
            double el = now() - t0; if (el > secs) break;
            double ph = fmod(el, COOL) / COOL; Tc = T0 * pow(T1 / T0, ph);
        }
        int idx = 1 + (int)(rnd() % (NL - 1));
        int x, ok;
        do { x = 1 + (int)(rnd() % (N - 1)); ok = 1; for (int k = 0; k < NL; k++) if (s[k] == x) ok = 0; } while (!ok);
        int s2[NL]; memcpy(s2, s, sizeof s2); s2[idx] = x;
        long long U2, M2; evaluate(s2, &U2, &M2); evals++;
        double E2 = U2 + W * M2;
        if (E2 <= E || urand() < exp(-(E2 - E) / Tc)) {
            memcpy(s, s2, sizeof s); E = E2; U = U2; Mg = M2; acc++;
            if (U < bestU || (U == bestU && Mg < bestMg)) { bestU = U; bestMg = Mg; memcpy(bestS, s, sizeof s); }
        }
    }
    double el = now() - t0;
    printf("RESULT N=%d n=%d W=%g seed=%s bestU=%lld bestMg=%lld S=%d,%d,%d,%d evals=%lld acc=%lld time=%.1f evals_per_s=%.0f\n",
           N, 2 * N, W, argv[3], bestU, bestMg, bestS[0], bestS[1], bestS[2], bestS[3], evals, acc, el, evals / el);
    char path[512];
    snprintf(path, sizeof path, "%s.txt", out);
    FILE *g = fopen(path, "w");
    fprintf(g, "N %d\nS %d %d %d %d\nU %lld\nMg %lld\n", N, bestS[0], bestS[1], bestS[2], bestS[3], bestU, bestMg);
    fclose(g);
    if (bestU == 0) { snprintf(path, sizeof path, "%s.edges", out); write_edges(bestS, path); printf("WROTE %s\n", path); }
    return 0;
}

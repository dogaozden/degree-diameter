/* tabann: annealing for Haar graphs H(G,S), |S| = d (s0 = e), on an arbitrary group given as a table file
 * (groups.py output: int32 N, then N*N uint16, row g: g*h, identity 0).
 * Cost = #vertices not within D of (e,A) + #not within D of (e,B)  (0 iff diameter <= D).
 * Usage: tabann TABLE d D secs seed OUT [START]     env: T0 (1.5), T1 (0.05), CYC (seconds per reheat cycle, 0=none)
 * OUT gets "best cost" and, on cost 0, an edge list OUT.edges (for apsp) and the S indices.
 * START file: whitespace-separated indices s1..s_{d-1} (resume).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int N, d, D;
static uint16_t *T;
static int *inv;
static int *vis, *queue;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int cost(const int *S) {
    int tot = 0;
    for (int src = 0; src < 2; src++) {
        memset(vis, 0, sizeof(int) * 2 * N);
        int h = 0, t = 0, level = 0, reached = 0;
        int start = src ? N : 0;
        vis[start] = 1; queue[t++] = start;
        while (h < t && level < D) {
            int end = t;
            while (h < end) {
                int v = queue[h++];
                if (v < N) {
                    for (int k = 0; k < d; k++) {
                        int w = T[(size_t)S[k] * N + v] + N;
                        if (!vis[w]) { vis[w] = 1; queue[t++] = w; }
                    }
                } else {
                    int g = v - N;
                    for (int k = 0; k < d; k++) {
                        int w = T[(size_t)inv[S[k]] * N + g];
                        if (!vis[w]) { vis[w] = 1; queue[t++] = w; }
                    }
                }
            }
            level++;
        }
        reached = t;
        tot += 2 * N - reached;
    }
    return tot;
}

static int inS(const int *S, int x, int upto) {
    for (int k = 0; k < upto; k++) if (S[k] == x) return 1;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: tabann TABLE d D secs seed OUT [START]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("table"); return 2; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 2; N = n32;
    T = malloc((size_t)N * N * 2);
    if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    d = atoi(argv[2]); D = atoi(argv[3]);
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[6];
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.5;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    double cyc = getenv("CYC") ? atof(getenv("CYC")) : 0;
    inv = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { inv[g] = h; break; }
    vis = malloc(sizeof(int) * 2 * N); queue = malloc(sizeof(int) * 2 * N);
    int *S = malloc(sizeof(int) * d), *Bst = malloc(sizeof(int) * d), *Tmp = malloc(sizeof(int) * d);
    S[0] = 0;
    if (argc >= 8) {
        FILE *g = fopen(argv[7], "r");
        for (int k = 1; k < d; k++) if (fscanf(g, "%d", &S[k]) != 1) { fprintf(stderr, "bad START\n"); return 2; }
        fclose(g);
    } else {
        for (int k = 1; k < d; k++) { int x; do x = rnd() % N; while (x == 0 || inS(S, x, k)); S[k] = x; }
    }
    int cur = cost(S), best = cur;
    memcpy(Bst, S, sizeof(int) * d);
    clock_t c0 = clock();
    double t0 = 0; long long it = 0;
    double cycStart = 0;
    double Tcur = T0;
    while (1) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            if (cyc > 0) { /* reheat cycles: T goes T0 -> T1 each cycle */
                if (el - cycStart >= cyc) cycStart = el;
                double fr = (el - cycStart) / cyc;
                Tcur = T0 * pow(T1 / T0, fr);
            } else {
                double fr = el / secs; Tcur = T0 * pow(T1 / T0, fr);
            }
            (void)t0;
        }
        it++;
        memcpy(Tmp, S, sizeof(int) * d);
        int k = 1 + rnd() % (d - 1);
        int x; do x = rnd() % N; while (x == 0 || inS(S, x, d));
        S[k] = x;
        int c = cost(S);
        int delta = c - cur;
        if (delta <= 0 || urand() < exp(-delta / Tcur)) {
            cur = c;
            if (cur < best) {
                best = cur; memcpy(Bst, S, sizeof(int) * d);
                fprintf(stderr, "it %lld best %d T %.3f S", it, best, Tcur);
                for (int q = 1; q < d; q++) fprintf(stderr, " %d", S[q]);
                fprintf(stderr, "\n");
                if (best == 0) break;
            }
        } else {
            memcpy(S, Tmp, sizeof(int) * d);
        }
    }
    double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
    printf("RESULT d=%d D=%d N=%d best=%d iters=%lld secs=%.1f S", d, D, N, best, it, el);
    for (int q = 1; q < d; q++) printf(" %d", Bst[q]);
    printf("\n");
    char fn[512];
    sprintf(fn, "%s.best", out);
    FILE *o = fopen(fn, "w");
    for (int q = 1; q < d; q++) fprintf(o, "%d ", Bst[q]);
    fprintf(o, "\n"); fclose(o);
    if (best == 0) {
        sprintf(fn, "%s.edges", out);
        FILE *e = fopen(fn, "w");
        fprintf(e, "%d\n", 2 * N);
        for (int g = 0; g < N; g++) for (int k = 0; k < d; k++)
            fprintf(e, "%d %d\n", g, N + T[(size_t)Bst[k] * N + g]);
        fclose(e);
        sprintf(fn, "%s.sol", out);
        o = fopen(fn, "w");
        fprintf(o, "d %d D %d N %d S", d, D, N);
        for (int q = 0; q < d; q++) fprintf(o, " %d", Bst[q]);
        fprintf(o, "\n"); fclose(o);
        printf("FOUND %s.edges\n", out);
    }
    return 0;
}

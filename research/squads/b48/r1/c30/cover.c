/* c30: canonical double covers (Haar-type) of Cayley tables.
   usage: cover TABLE.bin MODE SECONDS SEED OUT_PREFIX
   MODE canon : enumerate all inverse-closed 4-sets S (graph = (x,0)~(xs,1), S = S^-1)
   MODE haar  : random 4-sets S (general Haar graph, for comparison)
   Cost = #vertices at distance > 8 from (e,0) + from (e,1)  (by left-transitivity this is the
   full diameter test; cost 0 <=> diameter <= 8). Writes OUT_PREFIX.edges on cost 0 or at the end
   for the best S. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int N;
static uint16_t *T;      /* T[g*N+h] = g*h */
static int *inv;
static int S[4];
static int *dist, *queue;

#define M(g,h) T[(size_t)(g)*N+(h)]

static int cost_of(const int *s) {
    /* vertices: x -> x (side 0), N+y (side 1) */
    int V = 2 * N;
    int srcs[2] = {0, N};
    int total = 0;
    for (int q = 0; q < 2; q++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[srcs[q]] = 0; queue[tail++] = srcs[q];
        while (head < tail) {
            int v = queue[head++];
            int d = dist[v];
            if (d >= 8) continue;
            if (v < N) {
                int x = v;
                for (int i = 0; i < 4; i++) {
                    int w = N + M(x, s[i]);
                    if (dist[w] < 0) { dist[w] = d + 1; queue[tail++] = w; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < 4; i++) {
                    int w = M(y, inv[s[i]]);
                    if (dist[w] < 0) { dist[w] = d + 1; queue[tail++] = w; }
                }
            }
        }
        for (int v = 0; v < V; v++) if (dist[v] < 0) total++;
    }
    return total;
}

static void write_edges(const char *path, const int *s) {
    char buf[512];
    snprintf(buf, sizeof buf, "%s.edges", path);
    FILE *f = fopen(buf, "w");
    if (!f) return;
    fprintf(f, "%d\n", 2 * N);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < 4; i++)
            fprintf(f, "%d %d\n", x, N + M(x, s[i]));
    fclose(f);
}

#include <sys/time.h>
static double now(void) { struct timeval tv; gettimeofday(&tv, 0); return tv.tv_sec + tv.tv_usec * 1e-6; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("table"); return 1; }
    int32_t n32; fread(&n32, 4, 1, f); N = n32;
    T = malloc((size_t)N * N * sizeof(uint16_t));
    fread(T, sizeof(uint16_t), (size_t)N * N, f);
    fclose(f);
    const char *mode = argv[2];
    double secs = atof(argv[3]);
    unsigned seed = (unsigned)atoi(argv[4]);
    const char *outp = argv[5];
    srand(seed);
    inv = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (M(g, h) == 0) { inv[g] = h; break; }
    dist = malloc(2 * N * sizeof(int));
    queue = malloc(2 * N * sizeof(int));

    int *P = malloc(N * sizeof(int)), np = 0;   /* inverse pairs (rep g < inv g) */
    int *I = malloc(N * sizeof(int)), ni = 0;   /* involutions != e */
    for (int g = 1; g < N; g++) {
        if (inv[g] == g) I[ni++] = g;
        else if (g < inv[g]) P[np++] = g;
    }
    int best = 1 << 30; int bestS[4] = {0,0,0,0};
    long long evals = 0, zeros = 0;
    double t0 = now();
    if (strcmp(mode, "canon") == 0) {
        int done = 0;
        /* type A: two inverse pairs */
        for (int i = 0; i < np && !done; i++)
            for (int j = i + 1; j < np && !done; j++) {
                S[0] = P[i]; S[1] = inv[P[i]]; S[2] = P[j]; S[3] = inv[P[j]];
                int c = cost_of(S); evals++;
                if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
                if (c == 0) { zeros++; done = 1; }
                if ((evals & 1023) == 0 && now() - t0 > secs) done = 2;
            }
        /* type B: one pair + two involutions */
        for (int i = 0; i < np && !done; i++)
            for (int j = 0; j < ni && !done; j++)
                for (int k = j + 1; k < ni && !done; k++) {
                    S[0] = P[i]; S[1] = inv[P[i]]; S[2] = I[j]; S[3] = I[k];
                    int c = cost_of(S); evals++;
                    if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
                    if (c == 0) { zeros++; done = 1; }
                    if ((evals & 1023) == 0 && now() - t0 > secs) done = 2;
                }
        /* type C: four involutions */
        for (int a = 0; a < ni && !done; a++)
            for (int b = a + 1; b < ni && !done; b++)
                for (int c2 = b + 1; c2 < ni && !done; c2++)
                    for (int d = c2 + 1; d < ni && !done; d++) {
                        S[0] = I[a]; S[1] = I[b]; S[2] = I[c2]; S[3] = I[d];
                        int c = cost_of(S); evals++;
                        if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
                        if (c == 0) { zeros++; done = 1; }
                        if ((evals & 1023) == 0 && now() - t0 > secs) done = 2;
                    }
        printf("MODE canon N=%d np=%d ni=%d evals=%lld exhaustive=%s zeros=%lld\n", N, np, ni, evals,
               done == 2 ? "no(time)" : "yes", zeros);
    } else if (strcmp(mode, "hill") == 0) {
        /* general Haar graph S (not inverse-closed): hill climb with plateau moves and restarts */
        int cur = 1 << 30, cS[4];
        long long since = 0;
        while (now() - t0 < secs) {
            if (cur == 1 << 30 || since > 20000) {
                int ok = 0;
                while (!ok) {
                    for (int i = 0; i < 4; i++) cS[i] = 1 + rand() % (N - 1);
                    ok = 1;
                    for (int i = 0; i < 4 && ok; i++) for (int j = i + 1; j < 4; j++) if (cS[i] == cS[j]) { ok = 0; break; }
                }
                memcpy(S, cS, sizeof S);
                cur = cost_of(S); evals++; since = 0;
                if (cur < best) { best = cur; memcpy(bestS, S, sizeof S); }
                continue;
            }
            int i = rand() % 4, g = 1 + rand() % (N - 1);
            int ok = 1;
            for (int j = 0; j < 4; j++) if (S[j] == g) ok = 0;
            if (!ok) continue;
            int keep = S[i]; S[i] = g;
            int c = cost_of(S); evals++; since++;
            if (c <= cur) {
                if (c < cur) since = 0;
                cur = c;
                if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
                if (c == 0) { zeros++; break; }
            } else S[i] = keep;
        }
        printf("MODE hill N=%d evals=%lld zeros=%lld\n", N, evals, zeros);
    } else {
        /* haar: random 4-subsets of G\{e} */
        while (now() - t0 < secs) {
            int ok = 0;
            while (!ok) {
                for (int i = 0; i < 4; i++) S[i] = 1 + rand() % (N - 1);
                ok = 1;
                for (int i = 0; i < 4 && ok; i++) for (int j = i + 1; j < 4; j++) if (S[i] == S[j]) { ok = 0; break; }
            }
            int c = cost_of(S); evals++;
            if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
            if (c == 0) { zeros++; break; }
        }
        printf("MODE haar N=%d evals=%lld zeros=%lld\n", N, evals, zeros);
    }
    printf("BEST cost=%d miss=%.3f S=%d,%d,%d,%d time=%.1fs\n", best, best / 2.0, bestS[0], bestS[1], bestS[2], bestS[3], now() - t0);
    if (best < (1 << 30)) write_edges(outp, bestS);
    return 0;
}

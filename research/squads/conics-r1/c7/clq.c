/* Max clique for card c7.  usage:
     clq exact <adj.bin> <seconds>            exact MCQ (Tomita-style coloring bound), clique forced to contain vertex 0
     clq ts    <adj.bin> <seconds> <seed>     tabu search (MN/TS-like: add / swap / drop with tabu tenure), restarts
   adj.bin = int32 N, then N*N uint8 adjacency (0/1, symmetric, zero diagonal).
   Prints best clique size and vertex list. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int N, W;
static uint64_t *ADJ;      /* N*W bitsets */
static unsigned char *A;
static int best_n = 0;
static int *best, *cur, cur_n = 0;
static long long nodes = 0;
static double tlim;
static clock_t t0;
static int timed_out = 0;

static double now(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static void expand(uint64_t *P, int depth) {
    int n = 0;
    for (int w = 0; w < W; w++) n += __builtin_popcountll(P[w]);
    if (n == 0) return;
    int *order = malloc(sizeof(int) * n), *col = malloc(sizeof(int) * n);
    uint64_t *Q = malloc(8 * W), *R = malloc(8 * W);
    memcpy(Q, P, 8 * W);
    int k = 0, color = 0, remaining = n;
    while (remaining > 0) {
        color++;
        memcpy(R, Q, 8 * W);
        for (int w = 0; w < W; w++) {
            while (R[w]) {
                int b = __builtin_ctzll(R[w]);
                int v = w * 64 + b;
                uint64_t bit = 1ULL << b;
                R[w] &= ~bit; Q[w] &= ~bit;
                for (int x = 0; x < W; x++) R[x] &= ~ADJ[(size_t)v * W + x];
                order[k] = v; col[k] = color; k++; remaining--;
                w = w; /* keep scanning this word; R[w] may have been cleared of higher bits */
            }
        }
    }
    uint64_t *NP = malloc(8 * W);
    uint64_t *PP = malloc(8 * W);
    memcpy(PP, P, 8 * W);
    for (int i = k - 1; i >= 0; i--) {
        if (cur_n + col[i] <= best_n) break;
        if (timed_out) break;
        if ((++nodes & 1023) == 0 && now() > tlim) { timed_out = 1; break; }
        int v = order[i];
        cur[cur_n++] = v;
        for (int x = 0; x < W; x++) NP[x] = PP[x] & ADJ[(size_t)v * W + x];
        int empty = 1;
        for (int x = 0; x < W; x++) if (NP[x]) { empty = 0; break; }
        if (empty) {
            if (cur_n > best_n) {
                best_n = cur_n;
                memcpy(best, cur, sizeof(int) * cur_n);
                fprintf(stderr, "exact: new best %d at t=%.1f\n", best_n, now());
            }
        } else {
            expand(NP, depth + 1);
        }
        cur_n--;
        PP[v >> 6] &= ~(1ULL << (v & 63));
    }
    free(NP); free(PP); free(order); free(col); free(Q); free(R);
}

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int *gC, *gmiss, gcn;
static char *ginC;
static void addv(int x) {
    ginC[x] = 1; gC[gcn++] = x;
    for (int v = 0; v < N; v++) if (v != x && !A[(size_t)x * N + v]) gmiss[v]++;
}
static int dropv(int idx) { /* removes C[idx], returns the vertex */
    int x = gC[idx];
    gC[idx] = gC[gcn - 1]; gcn--;
    ginC[x] = 0;
    for (int v = 0; v < N; v++) if (v != x && !A[(size_t)x * N + v]) gmiss[v]--;
    return x;
}

static void tabu(double seconds, unsigned long long seed, long long L) {
    rs = seed * 2654435761ULL + 1;
    gmiss = calloc(N, sizeof(int));
    ginC = calloc(N, 1);
    gC = malloc(sizeof(int) * N); gcn = 0;
    long long *tabu_until = calloc(N, sizeof(long long));
    int *addl = malloc(sizeof(int) * N), *swl = malloc(sizeof(int) * N);
    long long it = 0, last_imp = 0;
    int local_best = 0;
    addv((int)(rnd() % N));
    while (now() < seconds) {
        it++;
        int na = 0, ns = 0;
        for (int v = 0; v < N; v++) {
            if (ginC[v]) continue;
            if (gmiss[v] == 0) { if (tabu_until[v] <= it || gcn + 1 > best_n) addl[na++] = v; }
            else if (gmiss[v] == 1) { if (tabu_until[v] <= it) swl[ns++] = v; }
        }
        if (na > 0) {
            addv(addl[rnd() % na]);
        } else if (ns > 0) {
            int v = swl[rnd() % ns];
            int wi = -1;
            for (int i = 0; i < gcn; i++) if (!A[(size_t)v * N + gC[i]]) { wi = i; break; }
            int w = dropv(wi);
            tabu_until[w] = it + 7 + (long long)(rnd() % (gcn + 1));
            addv(v);
        } else {
            int wi = (int)(rnd() % gcn);
            int w = dropv(wi);
            tabu_until[w] = it + 7 + (long long)(rnd() % (gcn + 1));
        }
        if (gcn > local_best) { local_best = gcn; last_imp = it; }
        if (gcn > best_n) {
            best_n = gcn; memcpy(best, gC, sizeof(int) * gcn);
            fprintf(stderr, "ts: new best %d at t=%.1f it=%lld\n", best_n, now(), it);
            last_imp = it;
        }
        if (it - last_imp > L) {  /* restart */
            while (gcn > 0) dropv(gcn - 1);
            memset(tabu_until, 0, sizeof(long long) * N);
            addv((int)(rnd() % N));
            local_best = 0; last_imp = it;
        }
    }
    fprintf(stderr, "ts: iterations %lld\n", it);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: clq exact|ts adj.bin seconds [seed]\n"); return 1; }
    FILE *f = fopen(argv[2], "rb");
    if (!f) { perror("open"); return 1; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 1;
    N = n32; W = (N + 63) / 64;
    A = malloc((size_t)N * N);
    if (fread(A, 1, (size_t)N * N, f) != (size_t)N * N) return 1;
    fclose(f);
    ADJ = calloc((size_t)N * W, 8);
    for (int v = 0; v < N; v++)
        for (int u = 0; u < N; u++)
            if (A[(size_t)v * N + u]) ADJ[(size_t)v * W + (u >> 6)] |= 1ULL << (u & 63);
    best = malloc(sizeof(int) * N); cur = malloc(sizeof(int) * N);
    tlim = atof(argv[3]);
    t0 = clock();
    if (strcmp(argv[1], "exact") == 0) {
        /* vertex transitive (Cayley graph): WLOG clique contains vertex 0 */
        uint64_t *P = calloc(W, 8);
        for (int u = 0; u < N; u++) if (A[u]) P[u >> 6] |= 1ULL << (u & 63);
        cur[0] = 0; cur_n = 1; best_n = 1; best[0] = 0;
        expand(P, 1);
        printf("exact: max clique containing vertex 0 = %d (timed_out=%d, nodes=%lld, time=%.1fs)\n",
               best_n, timed_out, nodes, now());
    } else {
        unsigned long long seed = argc > 4 ? strtoull(argv[4], 0, 10) : 1;
        tabu(tlim, seed, 4000);
        printf("ts: best clique size %d\n", best_n);
    }
    printf("clique:");
    for (int i = 0; i < best_n; i++) printf(" %d", best[i]);
    printf("\n");
    return 0;
}

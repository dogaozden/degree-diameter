/* hk.c: perfect matching of the point side of a regular bipartite graph (Hopcroft-Karp, random greedy start).
   Input (binary int32): N D, then N*D adjacency entries (line ids of each point).
   Usage: hk IN OUT SEED   Output (binary int32): mate[p] = line matched to point p (-1 if unmatched). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int N, D;
static int *adj, *mateL, *mateR, *dist, *queue, *it, *stk;

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int bfs(void) {
    int qh = 0, qt = 0, found = 0;
    for (int p = 0; p < N; p++) { if (mateL[p] < 0) { dist[p] = 0; queue[qt++] = p; } else dist[p] = -1; }
    while (qh < qt) {
        int p = queue[qh++];
        for (int k = 0; k < D; k++) {
            int l = adj[(size_t)p * D + k];
            int p2 = mateR[l];
            if (p2 < 0) found = 1;
            else if (dist[p2] < 0) { dist[p2] = dist[p] + 1; queue[qt++] = p2; }
        }
    }
    return found;
}

static int dfs(int root) {
    int sp = 0;
    stk[sp++] = root;
    while (sp > 0) {
        int p = stk[sp - 1];
        if (it[p] >= D) { dist[p] = -2; sp--; continue; }
        int l = adj[(size_t)p * D + it[p]];
        it[p]++;
        int p2 = mateR[l];
        if (p2 < 0) {
            for (int j = sp - 1; j >= 0; j--) {
                int pj = stk[j];
                int lj = adj[(size_t)pj * D + it[pj] - 1];
                mateL[pj] = lj; mateR[lj] = pj;
            }
            return 1;
        } else if (dist[p2] == dist[p] + 1) {
            stk[sp++] = p2;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: hk IN OUT SEED\n"); return 2; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("in"); return 2; }
    int hdr[2];
    if (fread(hdr, 4, 2, f) != 2) return 2;
    N = hdr[0]; D = hdr[1];
    adj = malloc(sizeof(int) * (size_t)N * D);
    if (fread(adj, 4, (size_t)N * D, f) != (size_t)N * D) { fprintf(stderr, "short read\n"); return 2; }
    fclose(f);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    mateL = malloc(sizeof(int) * N); mateR = malloc(sizeof(int) * N);
    dist = malloc(sizeof(int) * N); queue = malloc(sizeof(int) * N);
    it = malloc(sizeof(int) * N); stk = malloc(sizeof(int) * (N + 1));
    for (int p = 0; p < N; p++) mateL[p] = -1;
    for (int l = 0; l < N; l++) mateR[l] = -1;
    /* random greedy start: random point order, random rotation of its adjacency */
    int *ord = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) ord[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
    for (int i = 0; i < N; i++) {
        int p = ord[i];
        int r = rnd() % D;
        for (int k = 0; k < D; k++) {
            int l = adj[(size_t)p * D + (k + r) % D];
            if (mateR[l] < 0) { mateL[p] = l; mateR[l] = p; break; }
        }
    }
    int matched = 0; for (int p = 0; p < N; p++) matched += mateL[p] >= 0;
    fprintf(stderr, "greedy matched %d of %d\n", matched, N);
    int phases = 0;
    while (bfs()) {
        for (int p = 0; p < N; p++) it[p] = 0;
        int aug = 0;
        for (int p = 0; p < N; p++) if (mateL[p] < 0) aug += dfs(p);
        phases++;
        matched = 0; for (int q = 0; q < N; q++) matched += mateL[q] >= 0;
        fprintf(stderr, "phase %d: augmented %d, matched %d\n", phases, aug, matched);
        if (aug == 0) break;
    }
    matched = 0; for (int p = 0; p < N; p++) matched += mateL[p] >= 0;
    fprintf(stderr, "final matched %d of %d\n", matched, N);
    f = fopen(argv[2], "wb");
    fwrite(mateL, 4, N, f);
    fclose(f);
    return matched == N ? 0 : 1;
}

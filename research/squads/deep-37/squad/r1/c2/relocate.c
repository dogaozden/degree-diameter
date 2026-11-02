/* relocate.c (deep-37, squad r1, card c2): exhaustive pair-relocation neighbourhood of a 170-vertex cubic bipartite graph.
   For each edge x-y (x side 0, y side 1) of the 170 graph with index in [START, END):
     delete the pair x,y, reconnect the four freed ends a1,a2 (of y) and b1,b2 (of x) by either a1-b1,a2-b2 (c=0)
     or a1-b2,a2-b1 (c=1) (must be new edges): a 168-vertex cubic bipartite graph G';
     then exhaustively insert a new pair into G' (2-edge insertion: remove two edges, add x'-b_i, x'-b_j, x'-y',
     y'-a_i, y'-a_j) and score every insertion by far (pairs at distance > 7).
   Prints the best far per (edge, c) and the global best; writes the global best graph to OUT.
   usage: relocate GRAPH170 OUT START END */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXN 192
#define W 3
#define MAXM 300

static int adj[MAXN][3];
static uint64_t R[2][MAXN][W];
static uint64_t mask[W];
static int N_;

static int far_of(int N, int M, const int *ea, const int *eb) {
    int dc[MAXN]; memset(dc, 0, sizeof dc);
    for (int i = 0; i < M; i++) { int a = ea[i], b = eb[i];
        adj[a][dc[a]++] = b; adj[b][dc[b]++] = a; }
    memset(mask, 0, sizeof mask);
    for (int v = 0; v < N; v++) mask[v >> 6] |= 1ULL << (v & 63);
    int cur = 0;
    memset(R[0], 0, sizeof R[0]);
    for (int v = 0; v < N; v++) R[0][v][v >> 6] |= 1ULL << (v & 63);
    for (int it = 0; it < 7; it++) {
        int nx = cur ^ 1;
        for (int v = 0; v < N; v++) {
            int a = adj[v][0], b = adj[v][1], c = adj[v][2];
            for (int w = 0; w < W; w++) R[nx][v][w] = R[cur][v][w] | R[cur][a][w] | R[cur][b][w] | R[cur][c][w];
        }
        cur = nx;
    }
    int far = 0;
    for (int v = 0; v < N; v++) for (int w = 0; w < W; w++) {
        uint64_t miss = ~R[cur][v][w] & mask[w];
        far += __builtin_popcountll(miss);
    }
    /* ordered count minus the diagonal (each v reaches itself, so it is not missing) */
    return far / 2;
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int isedge_list(const int *ea, const int *eb, int M, int a, int b) {
    for (int i = 0; i < M; i++) if ((ea[i] == a && eb[i] == b)) return 1;
    return 0;
}

static void save(const char *fn, int N, int M, const int *ea, const int *eb) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); exit(1); }
    fprintf(f, "%d\n", N);
    for (int i = 0; i < M; i++) fprintf(f, "%d %d\n", ea[i], eb[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: relocate GRAPH170 OUT START END\n"); return 2; }
    int start = atoi(argv[3]), end = atoi(argv[4]);
    FILE *f = fopen(argv[1], "r"); int n0; if (fscanf(f, "%d", &n0) != 1) return 2;
    int A[MAXM], B[MAXM], m0 = 0, a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { A[m0] = a; B[m0] = b; m0++; }
    fclose(f);
    if (n0 != 170) { fprintf(stderr, "need a 170-vertex graph\n"); return 2; }
    int col[MAXN]; for (int i = 0; i < n0; i++) col[i] = -1; col[0] = 0;
    for (int it = 0; it < n0; it++) for (int i = 0; i < m0; i++) {
        if (col[A[i]] >= 0 && col[B[i]] < 0) col[B[i]] = 1 - col[A[i]];
        if (col[B[i]] >= 0 && col[A[i]] < 0) col[A[i]] = 1 - col[B[i]];
    }
    static int EA[MAXM], EB[MAXM];
    for (int i = 0; i < m0; i++) { if (col[A[i]] == 0) { EA[i] = A[i]; EB[i] = B[i]; } else { EA[i] = B[i]; EB[i] = A[i]; } }
    int gfar = far_of(170, m0, EA, EB);
    printf("input far=%d\n", gfar); fflush(stdout);

    int best_all = 1 << 30;
    double t0 = now();
    for (int e = start; e < end && e < m0; e++) {
        int x = EA[e], y = EB[e];   /* x side 0, y side 1 */
        int b1 = -1, b2 = -1, a1 = -1, a2 = -1;
        for (int i = 0; i < m0; i++) {
            if (EA[i] == x && EB[i] != y) { if (b1 < 0) b1 = EB[i]; else b2 = EB[i]; }
            if (EB[i] == y && EA[i] != x) { if (a1 < 0) a1 = EA[i]; else a2 = EA[i]; }
        }
        for (int c = 0; c < 2; c++) {
            int p1 = a1, q1 = c == 0 ? b1 : b2, p2 = a2, q2 = c == 0 ? b2 : b1;   /* new edges p1-q1, p2-q2 */
            /* build G' on vertices other than x, y, relabelled 0..167 */
            int lab[MAXN]; int k = 0;
            for (int v = 0; v < 170; v++) lab[v] = (v == x || v == y) ? -1 : k++;
            int GA[MAXM], GB[MAXM], gm = 0, ok = 1;
            for (int i = 0; i < m0; i++) {
                if (i == e || EA[i] == x || EB[i] == y || EA[i] == x || EB[i] == y) continue;
                GA[gm] = lab[EA[i]]; GB[gm] = lab[EB[i]]; gm++;
            }
            /* the four new edges must not be existing edges of G' */
            if (isedge_list(GA, GB, gm, lab[p1], lab[q1]) || isedge_list(GA, GB, gm, lab[p2], lab[q2])) ok = 0;
            if (p1 == p2 || q1 == q2) ok = 0;
            if (!ok) continue;
            GA[gm] = lab[p1]; GB[gm] = lab[q1]; gm++;
            GA[gm] = lab[p2]; GB[gm] = lab[q2]; gm++;
            /* sides: lab keeps the relative order; side of GA = 0, GB = 1 by construction */
            if (gm != 252) { fprintf(stderr, "bad G' size %d\n", gm); return 1; }
            /* exhaustive 2-edge insertion into G' */
            int best_e = 1 << 30; int bi = -1, bj = -1;
            static int HA[MAXM], HB[MAXM];
            for (int i = 0; i < gm; i++) for (int j = i + 1; j < gm; j++) {
                int ai = GA[i], bi_ = GB[i], aj = GA[j], bj_ = GB[j];
                if (ai == aj || bi_ == bj_) continue;
                int hm = 0;
                for (int t = 0; t < gm; t++) if (t != i && t != j) { HA[hm] = GA[t]; HB[hm] = GB[t]; hm++; }
                int xp = 168, yp = 169;
                HA[hm] = xp; HB[hm] = bi_; hm++;
                HA[hm] = xp; HB[hm] = bj_; hm++;
                HA[hm] = xp; HB[hm] = yp; hm++;
                HA[hm] = ai; HB[hm] = yp; hm++;
                HA[hm] = aj; HB[hm] = yp; hm++;
                /* skip if the inserted pair creates a multi-edge (cannot: x, y are new) */
                int fc = far_of(170, hm, HA, HB);
                if (fc < best_e) { best_e = fc; bi = i; bj = j; }
                if (fc < best_all) {
                    best_all = fc;
                    /* save the graph */
                    char fn[512]; snprintf(fn, sizeof fn, "%s", argv[2]);
                    save(fn, 170, hm, HA, HB);
                    printf("NEW far=%d edge=%d c=%d t=%.1f\n", fc, e, c, now() - t0); fflush(stdout);
                }
            }
            printf("edge %d c %d: best insertion far %d (i=%d j=%d)\n", e, c, best_e, bi, bj); fflush(stdout);
        }
    }
    printf("DONE best_all=%d t=%.1f\n", best_all, now() - t0);
    return 0;
}

/* r2d/nb1.c: exhaustive depth-1 neighbourhood of an equivariant (sigma-invariant) graph.
   usage: INIT_EDGES=... INIT_SIGMA=... ./nb1 n [outprefix]  -> histogram of far over all valid equivariant 2-switches,
   writes the best neighbour (if < start) to outprefix_nb.edges */
#define main main_inv
#include "inv.c"
#undef main
int main(int argc, char **argv) {
    n = atoi(argv[1]); m = n / 2; f = 0;
    rng_s[0] = 7; rng_s[1] = 9; for (int i = 0; i < 10; i++) rnd64();
    const char *ie = getenv("INIT_EDGES"), *is = getenv("INIT_SIGMA");
    FILE *fs = fopen(is, "r"); for (int v = 0; v < n; v++) if (fscanf(fs, "%d", &sg[v]) != 1) return 1; fclose(fs);
    for (int v = 0; v < m; v++) if (sg[v] == v) f++;
    FILE *fe = fopen(ie, "r"); int nn; if (fscanf(fe, "%d", &nn) != 1) return 1;
    memset(has, 0, sizeof has); for (int v = 0; v < n; v++) { deg[v] = 0; adj[v][0] = adj[v][1] = adj[v][2] = -1; }
    int a, b; while (fscanf(fe, "%d %d", &a, &b) == 2) add_edge(a, b); fclose(fe);
    long long start = far_cost(); printf("start far=%lld f=%d\n", start, f);
    static long hist[4096]; long long nvalid = 0, bestv = 1LL << 40; Move bestM; long nlow = 0;
    /* enumerate: e = (a,b) from A-slots, f = (c,d) from A-slots, unordered pairs of distinct edge-orbits */
    for (int A1 = 0; A1 < m; A1++) for (int j1 = 0; j1 < 3; j1++) {
        int A_b = adj[A1][j1]; if (A_b < 0) continue;
        for (int A2 = 0; A2 < m; A2++) for (int j2 = 0; j2 < 3; j2++) {
            int C2 = A2, D2 = adj[A2][j2]; if (D2 < 0) continue;
            Move M = {A1, A_b, C2, D2};
            if (!valid_move(&M)) continue;
            /* each move appears in several (e,f) orderings; keep all, it only costs time */
            apply_move(&M, +1); long long v = far_cost(); apply_move(&M, -1);
            nvalid++; if (v < 4096) hist[v]++;
            if (v < start) nlow++;
            if (v < bestv) { bestv = v; bestM = M; }
        }
    }
    printf("valid moves %lld, best neighbour far=%lld, neighbours with far<start: %ld\n", nvalid, bestv, nlow);
    printf("far histogram of neighbours (<= start+4):");
    for (long long v = 0; v <= start + 4 && v < 4096; v++) if (hist[v]) printf(" %lld:%ld", v, hist[v]);
    printf("\n");
    if (argc > 2 && bestv < start) { apply_move(&bestM, +1); char fn[512]; snprintf(fn, sizeof fn, "%s_nb.edges", argv[2]); write_graph(fn); printf("wrote %s far=%lld\n", fn, far_cost()); }
    return 0;
}

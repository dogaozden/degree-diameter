/* r2d/nb2.c: exhaustive depth-2 search from the plateau: for every equivariant 2-switch M1 that keeps far == start,
   enumerate all equivariant 2-switches M2 and record the best far. usage: INIT_EDGES INIT_SIGMA ./nb2 n outprefix */
#define main main_inv
#include "inv.c"
#undef main
static void enum_moves(Move *list, int *cnt, int cap) {
    *cnt = 0;
    for (int A1 = 0; A1 < m; A1++) for (int j1 = 0; j1 < 3; j1++) {
        int A_b = adj[A1][j1]; if (A_b < 0) continue;
        for (int A2 = 0; A2 < m; A2++) for (int j2 = 0; j2 < 3; j2++) {
            int D2 = adj[A2][j2]; if (D2 < 0) continue;
            Move M = {A1, A_b, A2, D2};
            if (*cnt < cap && valid_move(&M)) list[(*cnt)++] = M;
        }
    }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); m = n / 2; f = 0; const char *pre = argv[2];
    rng_s[0] = 7; rng_s[1] = 9; for (int i = 0; i < 10; i++) rnd64();
    const char *ie = getenv("INIT_EDGES"), *is = getenv("INIT_SIGMA");
    FILE *fs = fopen(is, "r"); for (int v = 0; v < n; v++) if (fscanf(fs, "%d", &sg[v]) != 1) return 1; fclose(fs);
    for (int v = 0; v < m; v++) if (sg[v] == v) f++;
    FILE *fe = fopen(ie, "r"); int nn; if (fscanf(fe, "%d", &nn) != 1) return 1;
    memset(has, 0, sizeof has); for (int v = 0; v < n; v++) { deg[v] = 0; adj[v][0] = adj[v][1] = adj[v][2] = -1; }
    int a, b; while (fscanf(fe, "%d %d", &a, &b) == 2) add_edge(a, b); fclose(fe);
    long long start = far_cost(); printf("start far=%lld f=%d\n", start, f); fflush(stdout);
    static Move L1[200000], L2[200000]; int c1, c2;
    enum_moves(L1, &c1, 200000);
    long long bestv = start, hist[64] = {0}; long long n1 = 0, nplat = 0;
    for (int i = 0; i < c1; i++) {
        apply_move(&L1[i], +1); long long v1 = far_cost();
        if (v1 <= start) {
            nplat++;
            enum_moves(L2, &c2, 200000);
            for (int j = 0; j < c2; j++) {
                apply_move(&L2[j], +1); long long v2 = far_cost(); apply_move(&L2[j], -1);
                n1++; if (v2 < 64) hist[v2]++;
                if (v2 < bestv) { bestv = v2; char fn[512]; snprintf(fn, sizeof fn, "%s_d2_%lld.edges", pre, v2); write_graph(fn);
                    printf("  new best %lld at plateau move %d / %d\n", v2, i, c1); fflush(stdout); }
            }
        }
        apply_move(&L1[i], -1);
        if (i % 5000 == 0) { printf("progress %d/%d plateau %lld evals %lld best %lld\n", i, c1, nplat, n1, bestv); fflush(stdout); }
    }
    printf("done: plateau nodes %lld, depth-2 evals %lld, best %lld; hist:", nplat, n1, bestv);
    for (int v = 0; v < 64; v++) if (hist[v]) printf(" %d:%lld", v, hist[v]);
    printf("\n");
    return 0;
}

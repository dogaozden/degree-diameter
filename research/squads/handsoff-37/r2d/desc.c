/* r2d/desc.c: exhaustive steepest descent with plateau walk in the sigma-invariant family.
   Each step enumerates ALL valid equivariant 2-switches (about 0.3 s at n = 170), takes the best one; if it is not
   better, it takes a uniformly random tie (far == current) so the walk moves along the plateau.
   usage: INIT_EDGES INIT_SIGMA ./desc n seconds outprefix */
#define main main_inv
#include "inv.c"
#undef main
#include <time.h>
static Move LM[200000];
static int enum_moves(void) {
    int c = 0;
    for (int A1 = 0; A1 < m; A1++) for (int j1 = 0; j1 < 3; j1++) {
        int A_b = adj[A1][j1]; if (A_b < 0) continue;
        for (int A2 = 0; A2 < m; A2++) for (int j2 = 0; j2 < 3; j2++) {
            int D2 = adj[A2][j2]; if (D2 < 0) continue;
            Move M = {A1, A_b, A2, D2};
            if (c < 200000 && valid_move(&M)) LM[c++] = M;
        }
    }
    return c;
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); m = n / 2; double secs = atof(argv[2]); const char *pre = argv[3];
    rng_s[0] = 1234; rng_s[1] = 5678; for (int i = 0; i < 10; i++) rnd64();
    const char *ie = getenv("INIT_EDGES"), *is = getenv("INIT_SIGMA");
    FILE *fs = fopen(is, "r"); for (int v = 0; v < n; v++) if (fscanf(fs, "%d", &sg[v]) != 1) return 1; fclose(fs);
    FILE *fe = fopen(ie, "r"); int nn; if (fscanf(fe, "%d", &nn) != 1) return 1;
    memset(has, 0, sizeof has); for (int v = 0; v < n; v++) { deg[v] = 0; adj[v][0] = adj[v][1] = adj[v][2] = -1; }
    int a, b; while (fscanf(fe, "%d %d", &a, &b) == 2) add_edge(a, b); fclose(fe);
    long long cur = far_cost(), best = cur, start = cur; time_t t0 = time(NULL); long steps = 0, ties = 0;
    printf("start far=%lld\n", cur); fflush(stdout);
    while (difftime(time(NULL), t0) < secs) {
        int c = enum_moves(); if (c == 0) break;
        long long bv = 1LL << 40; int nb = 0; static int bestidx[200000];
        static long long vals[200000];
        for (int i = 0; i < c; i++) {
            apply_move(&LM[i], +1); long long v = far_cost(); apply_move(&LM[i], -1); vals[i] = v;
            if (v < bv) { bv = v; nb = 0; } if (v == bv) bestidx[nb++] = i;
        }
        int pick = bestidx[rndint(nb)];
        if (bv > cur) { /* no improving or tie move from the best: stop */ }
        if (bv < cur) { apply_move(&LM[pick], +1); cur = bv; }
        else if (bv == cur) { /* plateau: choose a random tie move among those equal to cur */
            int cnt = 0; for (int i = 0; i < c; i++) if (vals[i] == cur) cnt++;
            int r = rndint(cnt), pi = -1; for (int i = 0; i < c; i++) if (vals[i] == cur) { if (r == 0) { pi = i; break; } r--; }
            apply_move(&LM[pi], +1); ties++;
        } else break;
        steps++;
        if (cur < best) { best = cur; char fn[512]; snprintf(fn, sizeof fn, "%s_best.edges", pre); write_graph(fn);
            printf("step %ld t=%.0fs new best far=%lld (start %lld)\n", steps, difftime(time(NULL), t0), best, start); fflush(stdout); }
        if (steps % 50 == 0) { printf("step %ld t=%.0fs cur=%lld best=%lld ties=%ld moves=%d\n", steps, difftime(time(NULL), t0), cur, best, ties, c); fflush(stdout); }
    }
    printf("done: best far=%lld (start %lld) steps=%ld ties=%ld\n", best, start, steps, ties);
    return 0;
}

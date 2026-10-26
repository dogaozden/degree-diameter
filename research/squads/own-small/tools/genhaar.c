/* genhaar d: eval lines for the Haar base (2 vertices, d parallel edges; edge 0 is the tree edge = identity):
   S = {e, a, s_2, .., s_{d-1}} with a an Aut(G)-orbit rep != e (from stdin "N R rep...") and a < ... no: a fixed rep,
   the others strictly increasing and different from e and a. d = 3 or 4. */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
    int d = atoi(v[1]), N, R; if (scanf("%d %d", &N, &R) != 2) return 1;
    static int reps[8192]; for (int i = 0; i < R; i++) if (scanf("%d", &reps[i]) != 1) return 1;
    for (int i = 0; i < R; i++) { int a = reps[i]; if (!a) continue;
        if (d == 3) { for (int b = 1; b < N; b++) if (b != a) printf("0 %d %d\n", a, b); }
        else for (int b = 1; b < N; b++) if (b != a) for (int cc = b + 1; cc < N; cc++) if (cc != a) printf("0 %d %d %d\n", a, b, cc);
    }
    return 0;
}

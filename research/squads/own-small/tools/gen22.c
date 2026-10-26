/* gen22: eval lines for the 2+2 cubic base (b22_cubic.txt edge order 0-2,0-2,0-3,1-2,1-3,1-3): "0 a 0 0 b c" with
   a an Aut(G)-orbit rep != identity (read "N R rep..." from stdin) and 0 <= b < c < N (parallel edges 1-3 swapped). */
#include <stdio.h>
int main(void) {
    int N, R; if (scanf("%d %d", &N, &R) != 2) return 1;
    static int reps[4096]; for (int i = 0; i < R; i++) if (scanf("%d", &reps[i]) != 1) return 1;
    for (int i = 0; i < R; i++) { int a = reps[i]; if (!a) continue;
        for (int b = 0; b < N; b++) for (int c = b + 1; c < N; c++) printf("0 %d 0 0 %d %d\n", a, b, c); }
    return 0;
}

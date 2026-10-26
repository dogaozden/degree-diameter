/* h03: print eval lines "0 a 0 0 b c" for each class rep a (read from stdin, first token N, then R reps), all b, c in [0,N) */
#include <stdio.h>
int main(void) {
    int N, R; if (scanf("%d %d", &N, &R) != 2) return 1;
    int reps[1024]; for (int i = 0; i < R; i++) if (scanf("%d", &reps[i]) != 1) return 1;
    for (int i = 0; i < R; i++) {
        int a = reps[i];
        for (int b = 0; b < N; b++) for (int c = 0; c < N; c++) printf("0 %d 0 0 %d %d\n", a, b, c);
    }
    return 0;
}

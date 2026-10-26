/* gen N: prints all voltage lines "0 a 0 0 b c" for the 2+2 cubic base (edges 0,2,3 fixed at identity) */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    int N = atoi(argv[1]);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) for (int c = 0; c < N; c++)
        printf("0 %d 0 0 %d %d\n", a, b, c);
    return 0;
}

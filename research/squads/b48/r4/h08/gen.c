/* voltages for b22_cubic (edges 0..5): tree edges 0,2,3 = identity; free a=edge1, b=edge4 (1-3), c=edge5 (1-3), b<=c
   (the two parallel 1-3 edges are interchangeable). Prints "0 a 0 0 b c" lines for flift eval. */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    int N = atoi(argv[1]);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) for (int c = b; c < N; c++)
        printf("0 %d 0 0 %d %d\n", a, b, c);
    return 0;
}

/* Exhaustive cubic Haar graphs H(Z_N,{0,a,b}) for N in [Nlo,Nhi], diameter D.
   Vertices (g,0)->g, (g,1)->N+g; (g,0)~(g+s,1), s in S. Abelian: one BFS from (0,0) gives exact diameter.
   Normalization: S translated so 0 in S; one nonzero element scaled by a unit to a divisor d of N (d<N).
   Prints per N: min holes (vertices at distance > D from (0,0)) and a witness S when holes==0.
   Usage: abl3 Nlo Nhi D */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int Nlo = atoi(argv[1]), Nhi = atoi(argv[2]), D = atoi(argv[3]);
    int *dist = malloc(sizeof(int) * 2 * (Nhi + 1) * 2);
    int *q = malloc(sizeof(int) * 2 * (Nhi + 1) * 2);
    for (int N = Nlo; N <= Nhi; N++) {
        int V = 2 * N, bestholes = V + 1, ba = -1, bb = -1, found = 0;
        long cand = 0;
        for (int a = 1; a < N; a++) {
            if (N % a) continue;               /* a must divide N */
            for (int b = 1; b < N; b++) {
                if (b == a) continue;
                cand++;
                int S[3] = {0, a, b};
                for (int v = 0; v < V; v++) dist[v] = -1;
                int h = 0, t = 0;
                q[t++] = 0; dist[0] = 0;
                int reached = 1;
                while (h < t) {
                    int v = q[h++];
                    int dv = dist[v];
                    if (dv >= D) continue;
                    if (v < N) { /* (g,0) -> (g+s,1) */
                        int g = v;
                        for (int k = 0; k < 3; k++) {
                            int w = N + (g + S[k]) % N;
                            if (dist[w] < 0) { dist[w] = dv + 1; q[t++] = w; }
                        }
                    } else {     /* (g,1) -> (g-s,0) */
                        int g = v - N;
                        for (int k = 0; k < 3; k++) {
                            int w = (g - S[k] + N) % N;
                            if (dist[w] < 0) { dist[w] = dv + 1; q[t++] = w; }
                        }
                    }
                }
                int holes = V - t;
                if (holes < bestholes) { bestholes = holes; ba = a; bb = b; }
                if (holes == 0) { found = 1; break; }
            }
            if (found) break;
        }
        printf("N %d V %d cand %ld minholes %d S {0,%d,%d}%s\n", N, V, cand, bestholes, ba, bb,
               bestholes == 0 ? " SOLVED" : "");
        fflush(stdout);
    }
    return 0;
}

/* Bipartite exact-NB-4 controllers among Cayley graphs.
   Input (stdin): blocks "n id k", n lines of the multiplication table (0-based, row x col = x*y), k lines of 0/1
   membership vectors of index-2 subgroups G0. For each G0 and all a, b outside G0 (labels a, A=a^-1, b, B=b^-1),
   test whether the 108 label-reduced words of length 4 cover G0. Prints hits and the best coverage per group. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int T[256][256], inv_[256], n;
int main(int argc, char **argv) {
    int minside = argc > 1 ? atoi(argv[1]) : 1;
    int id, k;
    while (scanf("%d %d %d", &n, &id, &k) == 3) {
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (scanf("%d", &T[i][j]) != 1) return 1;
        int e = -1;
        for (int i = 0; i < n && e < 0; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i][j] != j) { ok = 0; break; } if (ok) e = i; }
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i][j] == e) inv_[i] = j;
        int best = 0, besta = -1, bestb = -1, bestsub = -1, hits = 0;
        for (int s = 0; s < k; s++) {
            int mem[256], g0 = 0;
            for (int i = 0; i < n; i++) { if (scanf("%d", &mem[i]) != 1) return 1; g0 += mem[i]; }
            if (g0 < minside) continue;
            int out[256], no = 0;
            for (int i = 0; i < n; i++) if (!mem[i]) out[no++] = i;
            for (int ia = 0; ia < no; ia++) for (int ib = 0; ib < no; ib++) {
                int L[4]; L[0] = out[ia]; L[1] = inv_[out[ia]]; L[2] = out[ib]; L[3] = inv_[out[ib]];
                /* label inverse: 0<->1, 2<->3 */
                static int seen[256]; memset(seen, 0, sizeof(int) * n); int cnt = 0;
                for (int t1 = 0; t1 < 4; t1++) { int x1 = L[t1];
                  for (int t2 = 0; t2 < 4; t2++) { if (t2 == (t1 ^ 1)) continue; int x2 = T[x1][L[t2]];
                    for (int t3 = 0; t3 < 4; t3++) { if (t3 == (t2 ^ 1)) continue; int x3 = T[x2][L[t3]];
                      for (int t4 = 0; t4 < 4; t4++) { if (t4 == (t3 ^ 1)) continue; int x4 = T[x3][L[t4]];
                        if (!seen[x4]) { seen[x4] = 1; cnt++; } } } } }
                if (cnt > best) { best = cnt; besta = out[ia]; bestb = out[ib]; bestsub = s; }
                if (cnt == g0) { hits++; if (hits <= 3) printf("HIT n=%d id=%d sub=%d |G0|=%d a=%d b=%d\n", n, id, s, g0, out[ia], out[ib]); }
            }
            printf("group %d %d sub %d |G0|=%d best=%d (a=%d b=%d) hits=%d\n", n, id, s, g0, best, besta, bestb, hits);
            best = 0; hits = 0;
        }
        fflush(stdout);
    }
    return 0;
}

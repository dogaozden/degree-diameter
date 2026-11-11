/* Bipartite Cayley controllers Cay(G, {a, a^-1, b, b^-1}) with a, b outside an index-2 subgroup G0:
   need (i) words of length <= 4 (any) cover G0 (same-side distance <= 4), (ii) a reduced relation of length 4
   (a 4-cycle at every vertex). Input as for ctrlsearch (tables + index-2 subgroup vectors). Prints hits. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int T[256][256], inv_[256], n;
int main(int argc, char **argv) {
    int id, k;
    while (scanf("%d %d %d", &n, &id, &k) == 3) {
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (scanf("%d", &T[i][j]) != 1) return 1;
        int e = -1; for (int i = 0; i < n && e < 0; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i][j] != j) { ok = 0; break; } if (ok) e = i; }
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i][j] == e) inv_[i] = j;
        for (int s = 0; s < k; s++) {
            int mem[256], g0 = 0; for (int i = 0; i < n; i++) { if (scanf("%d", &mem[i]) != 1) return 1; g0 += mem[i]; }
            int out[256], no = 0; for (int i = 0; i < n; i++) if (!mem[i]) out[no++] = i;
            int best = 0, hits = 0;
            for (int ia = 0; ia < no; ia++) for (int ib = ia; ib < no; ib++) {
                int a = out[ia], b = out[ib]; if (b == a || b == inv_[a]) continue;
                int L[4] = { a, inv_[a], b, inv_[b] };
                static int seen[256]; memset(seen, 0, sizeof(int) * n); int cnt = 0, rel4 = 0;
                seen[e] = 1; cnt = 1;
                for (int t1 = 0; t1 < 4; t1++) for (int t2 = 0; t2 < 4; t2++) { int x2 = T[L[t1]][L[t2]]; if (!seen[x2]) { seen[x2] = 1; cnt++; }
                    for (int t3 = 0; t3 < 4; t3++) for (int t4 = 0; t4 < 4; t4++) { int x4 = T[T[x2][L[t3]]][L[t4]]; if (!seen[x4]) { seen[x4] = 1; cnt++; }
                        if (x4 == e && t2 != (t1 ^ 1) && t3 != (t2 ^ 1) && t4 != (t3 ^ 1)) rel4 = 1; } }
                if (cnt > best) best = cnt;
                if (cnt == g0 && rel4) { hits++; if (hits <= 3) printf("HIT n=%d id=%d sub=%d |G0|=%d a=%d b=%d\n", n, id, s, g0, a, b); }
            }
            if (hits) printf("group %d %d sub %d |G0|=%d best=%d hits=%d\n", n, id, s, g0, best, hits);
            fflush(stdout);
        }
    }
    return 0; }

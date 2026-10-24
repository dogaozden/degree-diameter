/* Haar graphs H(G,S), |S| = 4, e in S: bipartite 4-regular, edges (g,A)~(sg,B).
   Want diameter <= 5 [(S^-1 S)^2 = G and (S S^-1)^2 = G] and a 4-cycle at every vertex
   [s2^-1 s1 = s3^-1 s4 with s1!=s2, s3!=s4, (s1,s2)!=(s4,s3)... i.e. a repeated quotient]. Exhaustive over S.
   Input: blocks "n id k" + table + k subgroup lines (subgroup lines ignored). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int T[256][256], inv_[256], n;
static int cover(int *S, int left) { /* left: words s_a^-1 s_b s_c^-1 s_d ; else s_a s_b^-1 s_c s_d^-1 */
    static int q[16], seen[256]; int nq = 0; memset(seen, 0, sizeof(int) * n);
    for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) q[nq++] = left ? T[inv_[S[a]]][S[b]] : T[S[a]][inv_[S[b]]];
    int cnt = 0; for (int i = 0; i < 16; i++) for (int j = 0; j < 16; j++) { int x = T[q[i]][q[j]]; if (!seen[x]) { seen[x] = 1; cnt++; } }
    return cnt; }
static int has4cycle(int *S) { /* quotients s_i^-1 s_j (i != j): a repeat among ordered pairs, excluding (i,j) vs (j,i) giving inverses */
    int q[4][4]; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) q[i][j] = T[inv_[S[i]]][S[j]];
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) for (int k = 0; k < 4; k++) for (int l = 0; l < 4; l++)
        if (k != l && !(i == k && j == l) && q[i][j] == q[k][l]) return 1;
    return 0; }
int main(int argc, char **argv) {
    int id, k, x;
    while (scanf("%d %d %d", &n, &id, &k) == 3) {
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (scanf("%d", &T[i][j]) != 1) return 1;
        for (int s = 0; s < k; s++) for (int i = 0; i < n; i++) if (scanf("%d", &x) != 1) return 1;
        int e = -1; for (int i = 0; i < n && e < 0; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i][j] != j) { ok = 0; break; } if (ok) e = i; }
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i][j] == e) inv_[i] = j;
        int best = 0, hits = 0, S[4]; S[0] = e;
        for (S[1] = 0; S[1] < n; S[1]++) if (S[1] != e)
        for (S[2] = S[1] + 1; S[2] < n; S[2]++) if (S[2] != e)
        for (S[3] = S[2] + 1; S[3] < n; S[3]++) if (S[3] != e) {
            if (!has4cycle(S)) continue;
            int c = cover(S, 1); if (c > best) best = c;
            if (c == n && cover(S, 0) == n) { hits++; if (hits <= 2) printf("HIT n=%d id=%d S={%d,%d,%d,%d}\n", n, id, S[0], S[1], S[2], S[3]); }
        }
        printf("group %d %d best=%d hits=%d\n", n, id, best, hits); fflush(stdout);
    }
    return 0; }

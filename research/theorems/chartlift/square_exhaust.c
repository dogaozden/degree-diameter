/* Exhaustive check: is there a cubic bipartite graph made of s disjoint 4-cycles ("squares", K_{2,2}) plus a perfect
   matching of external edges, with all same-side distances <= 4?  (CHART_LIFTS.md, Proposition 9: m = 18 needs one with
   s = 9.)  Within a square the two A-vertices (and the two B-vertices) are interchangeable, so the graph is determined up
   to isomorphism by the 2-in-2-out loopless digraph H on the squares (arc i -> j per external edge from an A-vertex of
   square i to a B-vertex of square j).  H = P1 + P2 for two derangements (Konig), and conjugating by a permutation of
   the squares we may take P1 to be a fixed representative of its cycle type.  So: for every cycle type of derangements
   of s points and every derangement P2, build the graph and test it.  Prints the number of valid graphs found.
   usage: square_exhaust s */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int s, m, n, adj[64][3], P1[16], P2[16], used[16];
long tested = 0, valid = 0;
static int check(void) {
    /* square i: A-vertices 2i, 2i+1; B-vertices m+2i, m+2i+1.  a_{i,0} -> B-vertex 0 of square P1(i);
       a_{i,1} -> B-vertex 1 of square P2(i) (the in-arc from P1 lands on b_{j,0}, from P2 on b_{j,1}). */
    for (int i = 0; i < s; i++) {
        for (int x = 0; x < 2; x++) { adj[2 * i + x][0] = m + 2 * i; adj[2 * i + x][1] = m + 2 * i + 1; adj[m + 2 * i + x][0] = 2 * i; adj[m + 2 * i + x][1] = 2 * i + 1; }
        adj[2 * i][2] = m + 2 * P1[i]; adj[m + 2 * P1[i]][2] = 2 * i;
        adj[2 * i + 1][2] = m + 2 * P2[i] + 1; adj[m + 2 * P2[i] + 1][2] = 2 * i + 1; }
    int dist[64], q[64];
    for (int st = 0; st < n; st++) {
        for (int i = 0; i < n; i++) dist[i] = -1; dist[st] = 0; int h = 0, t = 0; q[t++] = st;
        while (h < t) { int x = q[h++]; if (dist[x] >= 4) continue; for (int i = 0; i < 3; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        int lo = st < m ? 0 : m; for (int i = lo; i < lo + m; i++) if (dist[i] < 0) return 0; }
    return 1; }
static void rec(int i) {
    if (i == s) { tested++; if (check()) { valid++; if (valid <= 3) { printf("VALID P1="); for (int t = 0; t < s; t++) printf("%d", P1[t]); printf(" P2="); for (int t = 0; t < s; t++) printf("%d ", P2[t]); printf("\n"); } } return; }
    for (int j = 0; j < s; j++) if (!used[j] && j != i) { used[j] = 1; P2[i] = j; rec(i + 1); used[j] = 0; } }
/* cycle types of derangements: partitions of s into parts >= 2 */
int parts[16], np;
static void types(int left, int maxp) {
    if (left == 0) {
        int pos = 0; for (int c = 0; c < np; c++) { for (int t = 0; t < parts[c]; t++) P1[pos + t] = pos + (t + 1) % parts[c]; pos += parts[c]; }
        long v0 = valid, t0 = tested; memset(used, 0, sizeof used); rec(0);
        printf("cycle type"); for (int c = 0; c < np; c++) printf(" %d", parts[c]); printf(": %ld derangements P2 tested, %ld valid\n", tested - t0, valid - v0); fflush(stdout);
        return; }
    for (int p = (left < maxp ? left : maxp); p >= 2; p--) { parts[np++] = p; types(left - p, p); np--; } }
int main(int argc, char **argv) { s = atoi(argv[1]); m = 2 * s; n = 2 * m; np = 0; types(s, s);
    printf("s=%d (m=%d): %ld graphs tested, %ld with all same-side distances <= 4\n", s, m, tested, valid); return 0; }

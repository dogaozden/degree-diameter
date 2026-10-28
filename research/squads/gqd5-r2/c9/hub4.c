/* hub4: checks a hub graph. Input (stdin or file arg): "n m" then m lines "u v" (0-based).
   Checks: simple, bipartite (2-colouring from vertex 0), connected, and every pair of same-colour
   vertices at distance <= 4. Prints one line: RESULT valid=<0/1> n=.. nA=.. nB=.. maxdeg=.. m=.. bad=<#ordered bad pairs> */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = argc > 1 ? fopen(argv[1], "r") : stdin;
    if (!f) { printf("RESULT valid=0 error=open\n"); return 0; }
    int n, m;
    if (fscanf(f, "%d %d", &n, &m) != 2) { printf("RESULT valid=0 error=read\n"); return 0; }
    int *eu = malloc(sizeof(int) * m), *ev = malloc(sizeof(int) * m);
    int *deg = calloc(n, sizeof(int));
    for (int i = 0; i < m; i++) {
        if (fscanf(f, "%d %d", &eu[i], &ev[i]) != 2) { printf("RESULT valid=0 error=read\n"); return 0; }
        if (eu[i] < 0 || ev[i] < 0 || eu[i] >= n || ev[i] >= n || eu[i] == ev[i]) { printf("RESULT valid=0 error=range\n"); return 0; }
        deg[eu[i]]++; deg[ev[i]]++;
    }
    if (f != stdin) fclose(f);
    int *off = calloc(n + 1, sizeof(int));
    for (int i = 0; i < n; i++) off[i + 1] = off[i] + deg[i];
    int *pos = malloc(sizeof(int) * n); memcpy(pos, off, sizeof(int) * n);
    int *adj = malloc(sizeof(int) * 2 * m + 1);
    for (int i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    int maxdeg = 0; for (int i = 0; i < n; i++) if (deg[i] > maxdeg) maxdeg = deg[i];
    /* simple: no duplicate neighbours */
    int *mark = calloc(n, sizeof(int)); int simple = 1;
    for (int v = 0; v < n && simple; v++) {
        for (int k = off[v]; k < off[v + 1]; k++) { int w = adj[k]; if (mark[w] == v + 1) { simple = 0; break; } mark[w] = v + 1; }
    }
    /* 2-colour */
    int *col = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) col[i] = -1;
    int *q = malloc(sizeof(int) * n); int qh = 0, qt = 0; int bip = 1, reached = 0;
    if (n > 0) { col[0] = 0; q[qt++] = 0; }
    while (qh < qt) {
        int v = q[qh++]; reached++;
        for (int k = off[v]; k < off[v + 1]; k++) { int w = adj[k];
            if (col[w] < 0) { col[w] = 1 - col[v]; q[qt++] = w; }
            else if (col[w] == col[v]) bip = 0; }
    }
    int connected = (reached == n);
    int nA = 0, nB = 0; for (int i = 0; i < n; i++) { if (col[i] == 0) nA++; else if (col[i] == 1) nB++; }
    /* same-colour distance <= 4 */
    long bad = 0;
    int *dist = malloc(sizeof(int) * n); int *seen = calloc(n, sizeof(int)); int stamp = 0;
    int *cnt = malloc(sizeof(int) * 2);
    cnt[0] = nA; cnt[1] = nB;
    if (bip && connected) {
        for (int s = 0; s < n; s++) {
            stamp++; int h = 0, t = 0; int got = 0;
            q[t++] = s; seen[s] = stamp; dist[s] = 0;
            while (h < t) {
                int v = q[h++]; if (dist[v] >= 4) continue;
                for (int k = off[v]; k < off[v + 1]; k++) { int w = adj[k];
                    if (seen[w] != stamp) { seen[w] = stamp; dist[w] = dist[v] + 1; q[t++] = w;
                        if (col[w] == col[s]) got++; } }
            }
            if (got != cnt[col[s]] - 1) {
                /* count bad pairs for this s */
                bad += cnt[col[s]] - 1 - got;
            }
        }
    }
    int valid = simple && bip && connected && bad == 0 && maxdeg >= 0;
    printf("RESULT valid=%d n=%d nA=%d nB=%d maxdeg=%d m=%d simple=%d bip=%d connected=%d bad=%ld\n",
           valid, n, nA, nB, maxdeg, m, simple, bip, connected, bad);
    return 0;
}

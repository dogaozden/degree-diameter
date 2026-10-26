/* insert2: try to add two vertices to a valid cubic bipartite graph (own-small job).
   Remove edges a1-b1 and a2-b2 (a in side 0, b in side 1), add x (side 0) and y (side 1) with edges x-b1, x-b2, x-y,
   y-a1, y-a2: the graph stays cubic and bipartite with n+2 vertices. Checks diameter <= D exactly (BFS from every
   vertex, early abort). The first edge runs over edges incident to vertices 0..R-1 (orbit representatives when a
   group acts with fibres of size F: pass R = number of base vertices on side 0 times ... see usage), the second over all.
   Usage: insert2 EDGES D F   (first edge: an endpoint divisible by F, i.e. one edge per orbit when a group of order F acts
          semiregularly with vertex (u,g) = u*F + g and identity index 0; F = 1 tries all pairs)
   Prints "HIT e1 e2" for every success and a summary of the best (fewest far sources) attempt. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, m, *eu, *ev, adj[4096][3], deg[4096], side[4096];

static int far_sources(int N, int D, int (*A)[3]) {
    static int dist[4096], q[4096];
    int bad = 0;
    for (int s = 0; s < N; s++) {
        for (int i = 0; i < N; i++) dist[i] = -1;
        int h = 0, t = 0; dist[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; if (dist[x] >= D) continue;
            for (int j = 0; j < 3; j++) { int y = A[x][j]; if (y >= 0 && dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        if (t < N) { bad++; return bad; }   /* early abort: one far source is enough to reject */
    }
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: insert2 EDGES D FIRSTMAX\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]), FM = atoi(argv[3]);
    if (fscanf(f, "%d", &n) != 1) return 2;
    eu = malloc(sizeof(int) * 3 * n); ev = malloc(sizeof(int) * 3 * n); m = 0;
    while (fscanf(f, "%d %d", &eu[m], &ev[m]) == 2) m++;
    fclose(f);
    /* 2-colour */
    for (int i = 0; i < n; i++) { deg[i] = 0; side[i] = -1; }
    for (int e = 0; e < m; e++) { adj[eu[e]][deg[eu[e]]++] = ev[e]; adj[ev[e]][deg[ev[e]]++] = eu[e]; }
    { static int q[4096]; int h = 0, t = 0; side[0] = 0; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int j = 0; j < deg[x]; j++) { int y = adj[x][j]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } } }
    static int A[4096][3];
    long tried = 0, hits = 0;
    for (int e1 = 0; e1 < m; e1++) {
        if (eu[e1] % FM && ev[e1] % FM) continue;   /* first edge: an endpoint divisible by F (fibre representative) */
        for (int e2 = 0; e2 < m; e2++) {
            if (e2 == e1) continue;
            int a1 = side[eu[e1]] == 0 ? eu[e1] : ev[e1], b1 = a1 == eu[e1] ? ev[e1] : eu[e1];
            int a2 = side[eu[e2]] == 0 ? eu[e2] : ev[e2], b2 = a2 == eu[e2] ? ev[e2] : eu[e2];
            if (a1 == a2 || b1 == b2) continue;      /* x would get a double edge / y too */
            int N = n + 2, x = n, y = n + 1;
            for (int i = 0; i < n; i++) for (int j = 0; j < 3; j++) A[i][j] = adj[i][j];
            /* replace b1 in a1's list by y, a1 in b1's list by x, etc. */
            for (int j = 0; j < 3; j++) { if (A[a1][j] == b1) A[a1][j] = y; if (A[b1][j] == a1) A[b1][j] = x;
                                          if (A[a2][j] == b2) A[a2][j] = y; if (A[b2][j] == a2) A[b2][j] = x; }
            A[x][0] = b1; A[x][1] = b2; A[x][2] = y; A[y][0] = a1; A[y][1] = a2; A[y][2] = x;
            tried++;
            if (far_sources(N, D, A) == 0) { hits++; printf("HIT e1 %d (%d %d) e2 %d (%d %d)\n", e1, eu[e1], ev[e1], e2, eu[e2], ev[e2]); fflush(stdout); }
        }
    }
    printf("tried %ld hits %ld\n", tried, hits);
    return 0;
}

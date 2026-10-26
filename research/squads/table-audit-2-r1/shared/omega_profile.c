/* omega_profile.c (table-audit): where are the far pairs?  BFS from the hubs (p,0) and (p,0bar) for the given rows
   (default: all rows) and tabulate pairs at distance > D by (hub kind, target copy, target class, distance, and the
   target's H-distance to the same-row marks of its copy).  usage: omega_profile HEX TYPES INNER LAB D [ROWSTEP] */
#include "omega_model.h"
int main(int argc, char **argv) {
    Omega o; if (om_load_hex(&o, argv[1])) return 2; om_alloc(&o, argv[2], argv[3]);
    if (strcmp(argv[4], "id") && om_read_lab(&o, argv[4])) return 2;
    int D = atoi(argv[5]), step = argc > 6 ? atoi(argv[6]) : 1; om_build(&o);
    int n = o.n, C = o.C; long NV = o.NV;
    /* base distances from every vertex would be n^2: use BFS in base per needed vertex */
    long tab[2][64][2][4]; memset(tab, 0, sizeof tab);
    long dsame[2][7][7]; memset(dsame, 0, sizeof dsame);
    unsigned char *dist = malloc(NV); long *qu = malloc(sizeof(long) * NV);
    int *bd1 = malloc(sizeof(int) * 2 * n), *bd2 = malloc(sizeof(int) * 2 * n); int *bq = malloc(sizeof(int) * 2 * n);
    for (int t = 0; t < n; t += step) for (int bar = 0; bar < 2; bar++) {
        long s = om_hub(&o, t, bar, 0); memset(dist, 255, NV); dist[s] = 0; long h = 0, tl = 0; qu[tl++] = s;
        while (h < tl) { long x = qu[h++]; if (dist[x] > D) break; for (int j = 0; j < o.deg[x]; j++) { long y = o.adj[x * o.maxd + j]; if (dist[y] == 255) { dist[y] = dist[x] + 1; qu[tl++] = y; } } }
        for (int c = 0; c < C; c++) {
            long off = (long)c * 2 * n; int Pm = o.P[(long)c * n + t], Lm = n + o.L[(long)c * n + t];
            int done = 0;
            for (int v = 0; v < 2 * n; v++) { int d = dist[off + v]; if (d != 255 && d <= D) continue;
                int dd = d == 255 ? 3 : (d - D > 2 ? 2 : d - D - 1);
                tab[bar][c][v >= n][dd]++;
                if (!done) { /* base BFS from the two same-row marks */
                    for (int w = 0; w < 2; w++) { int *bd = w ? bd2 : bd1; int src = w ? Lm : Pm; for (int i = 0; i < 2 * n; i++) bd[i] = -1; bd[src] = 0; int hh = 0, tt = 0; bq[tt++] = src;
                        while (hh < tt) { int x = bq[hh++]; for (int j = 0; j < o.deg1; j++) { int y = o.badj[(long)x * o.deg1 + j]; if (bd[y] < 0) { bd[y] = bd[x] + 1; bq[tt++] = y; } } } }
                    done = 1; }
                dsame[bar][bd1[v]][bd2[v]]++;
            }
        }
    }
    for (int bar = 0; bar < 2; bar++) for (int c = 0; c < C; c++) for (int cl = 0; cl < 2; cl++) {
        long *T = tab[bar][c][cl]; if (T[0] + T[1] + T[2] + T[3] == 0) continue;
        printf("hub %s -> copy %2d (block %d type %c) %s: d=%d:%ld d=%d:%ld more:%ld unreached:%ld\n", bar ? "0bar" : "0   ", c, c / 5, o.types[c / 5], cl ? "lines " : "points", D + 1, T[0], D + 2, T[1], T[2], T[3]);
    }
    for (int bar = 0; bar < 2; bar++) for (int a = 0; a < 7; a++) for (int b = 0; b < 7; b++) if (dsame[bar][a][b]) printf("hub %s far target at H-dist %d from same-row point, %d from same-row line: %ld\n", bar ? "0bar" : "0", a, b, dsame[bar][a][b]);
    return 0;
}

/* Exhaustive single-orbit (Haar) controllers for a REAL per-edge chart on base_k1 (4 parallel edges, letter = edge).
   Cost as mlift_ejoint2 with DIAGBT=1 and a backtrack-complete, pencil-complete chart: same-side pair covered iff
   distance 2 (2-walk, value != e), or a nonsingular NB 4-walk, or the diagonal (free).  v0 = e WLOG (left translation
   fixes A-side values and conjugates B-side values).  Pattern file = echart -p output ("S A e1 e2 e3 e4", "S B ...";
   it must report no pencil failure and no missing diagonal point).
   usage: exh_k1r TABLE PATTERNS [maxprint]   -> min cost and up to maxprint optimal tuples (v0..v3 element indices) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int n; if (!f || fscanf(f, "%d", &n) != 1) return 2;
    int *T = malloc(sizeof(int) * n * n), *Inv = malloc(sizeof(int) * n), e = -1;
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 3;
    fclose(f);
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e) Inv[i] = j;
    static int singA[4][4][4][4], singB[4][4][4][4]; char line[256];
    f = fopen(argv[2], "r"); if (!f) return 4;
    while (fgets(line, sizeof line, f)) { char s, side; int a, b, c, d;
        if (sscanf(line, "%c %c %d %d %d %d", &s, &side, &a, &b, &c, &d) == 6 && s == 'S') { if (side == 'A') singA[a][b][c][d] = 1; else singB[a][b][c][d] = 1; }
        else if (line[0] == 'P' || line[0] == 'D') { fprintf(stderr, "chart has pencil/diagonal failures; not supported\n"); return 5; } }
    fclose(f);
    int maxprint = argc > 3 ? atoi(argv[3]) : 5;
    int W[256][4], nw = 0;
    for (int p0 = 0; p0 < 4; p0++) for (int p1 = 0; p1 < 4; p1++) if (p1 != p0) for (int p2 = 0; p2 < 4; p2++) if (p2 != p1)
        for (int p3 = 0; p3 < 4; p3++) if (p3 != p2) { W[nw][0] = p0; W[nw][1] = p1; W[nw][2] = p2; W[nw][3] = p3; nw++; }
    unsigned char *hA = malloc(n), *hB = malloc(n); int best = 1 << 30, nbest = 0; long cnt = 0; int v[4]; v[0] = e;
    for (int a = 0; a < n; a++) { if (a == e) continue;
      for (int b = 0; b < n; b++) { if (b == e || b == a) continue;
        for (int c = 0; c < n; c++) { if (c == e || c == a || c == b) continue;
          v[1] = a; v[2] = b; v[3] = c; memset(hA, 0, n); memset(hB, 0, n); hA[e] = hB[e] = 1;
          for (int p = 0; p < 4; p++) for (int q = 0; q < 4; q++) if (p != q) { hA[T[Inv[v[q]] * n + v[p]]] = 1; hB[T[v[q] * n + Inv[v[p]]]] = 1; }
          for (int w = 0; w < nw; w++) { int *P = W[w];
            if (!singA[P[0]][P[1]][P[2]][P[3]]) hA[T[Inv[v[P[3]]] * n + T[v[P[2]] * n + T[Inv[v[P[1]]] * n + v[P[0]]]]]] = 1;
            if (!singB[P[0]][P[1]][P[2]][P[3]]) hB[T[v[P[3]] * n + T[Inv[v[P[2]]] * n + T[v[P[1]] * n + Inv[v[P[0]]]]]]] = 1; }
          int c2 = 0; for (int t = 0; t < n; t++) c2 += !hA[t] + !hB[t];
          cnt++;
          if (c2 < best) { best = c2; nbest = 0; }
          if (c2 == best && nbest < maxprint) { printf("cost %d v=%d,%d,%d,%d\n", c2, v[0], v[1], v[2], v[3]); nbest++; }
        } } }
    printf("n=%d tuples=%ld min_cost=%d\n", n, cnt, best);
    return 0;
}

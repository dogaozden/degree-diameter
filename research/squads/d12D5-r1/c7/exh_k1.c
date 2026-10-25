/* Exhaustive FAKE-chart cost for a single-orbit base (k=1: four parallel base edges, voltages v0..v3 in G).
   Walk values (A-side): 2-walk v1^-1 v0 (value != 1), 4-walk v3^-1 v2 v1^-1 v0 with consecutive edges distinct.
   Left translation v_i -> g v_i leaves all walk values fixed, so v0 = 1 WLOG; enumerate distinct v1,v2,v3.
   usage: exh_k1 TABLE    prints the minimum number of uncovered group elements (fake cost, a lower bound for any chart). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int n; if (!f || fscanf(f, "%d", &n) != 1) return 2;
    int *T = malloc(sizeof(int) * n * n), *Inv = malloc(sizeof(int) * n), *hit = malloc(sizeof(int) * n), e = -1;
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 3;
    fclose(f);
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e) Inv[i] = j;
    int best = 1 << 30, bv[4] = {0, 0, 0, 0}; long cnt = 0; int v[4]; v[0] = e;
    for (int a = 0; a < n; a++) { if (a == e) continue;
      for (int b = 0; b < n; b++) { if (b == e || b == a) continue;
        for (int c = 0; c < n; c++) { if (c == e || c == a || c == b) continue;
          v[1] = a; v[2] = b; v[3] = c; memset(hit, 0, sizeof(int) * n);
          for (int p = 0; p < 4; p++) for (int q = 0; q < 4; q++) if (p != q) { int g = T[Inv[v[q]] * n + v[p]]; if (g != e) hit[g] = 1; }
          for (int p0 = 0; p0 < 4; p0++) for (int p1 = 0; p1 < 4; p1++) if (p1 != p0)
          for (int p2 = 0; p2 < 4; p2++) if (p2 != p1) for (int p3 = 0; p3 < 4; p3++) if (p3 != p2) {
            int t1 = T[Inv[v[p1]] * n + v[p0]], t2 = T[v[p2] * n + t1], g = T[Inv[v[p3]] * n + t2]; hit[g] = 1; }
          int c2 = 0; for (int t = 0; t < n; t++) c2 += !hit[t];
          cnt++;
          if (c2 < best) { best = c2; memcpy(bv, v, sizeof v); }
        } } }
    printf("n=%d tuples=%ld min_fake_cost=%d at v=(%d,%d,%d,%d)\n", n, cnt, best, bv[0], bv[1], bv[2], bv[3]);
    return 0;
}

/* Enumerate regular tournaments on n = 2r+1 vertices (all labelled ones, or with N+(0) = {1..r} if argv[2]=1),
   and for every typing in {H,D}^n record the profile: which (type, #friendly out-arcs) and (type, #friendly in-arcs)
   occur.  min alpha + min beta depends only on the profile.  Prints the count and the distinct profiles. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n, r, fix, np; int pi[64], pj[64]; int out[16][16]; int od[16], id_[16]; long count = 0;
unsigned char *seen;
static void record(void) {
  count++;
  for (int typ = 0; typ < (1 << n); typ++) {
    unsigned key = 0;
    for (int v = 0; v < n; v++) {
      int tv = (typ >> v) & 1, fo = 0, fi = 0;
      for (int w = 0; w < n; w++) if (w != v && (((typ >> w) & 1) != tv)) { if (out[v][w]) fo++; else fi++; }
      key |= 1u << (tv * (r + 1) + fo);                    /* alpha profile bits: 0..2r+1 */
      key |= 1u << (2 * (r + 1) + tv * (r + 1) + fi);      /* beta profile bits */
    }
    seen[key] = 1;
  }
}
static void rec(int k) {
  if (k == np) { record(); return; }
  int i = pi[k], j = pj[k];
  for (int d = 0; d < 2; d++) {
    int a = d ? j : i, b = d ? i : j;  /* arc a -> b */
    if (fix && i == 0) { if ((j <= r) != (a == 0)) continue; }
    if (od[a] == r || id_[b] == r) continue;
    od[a]++; id_[b]++; out[a][b] = 1; out[b][a] = 0;
    rec(k + 1);
    od[a]--; id_[b]--; out[a][b] = 0;
  }
}
int main(int argc, char **argv) {
  n = atoi(argv[1]); r = (n - 1) / 2; fix = argc > 2 ? atoi(argv[2]) : 0;
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) { pi[np] = i; pj[np] = j; np++; }
  seen = calloc(1u << (4 * (r + 1)), 1);
  rec(0);
  printf("n=%d tournaments=%ld\n", n, count);
  for (unsigned key = 0; key < (1u << (4 * (r + 1))); key++) if (seen[key]) printf("%u\n", key);
  return 0;
}

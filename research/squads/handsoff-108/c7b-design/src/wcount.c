/* wcount.c (worker c7b): non-backtracking walk multiplicities of a cyclic lift of H(q) + J matchings.
 * For a point source p0 (copy 0), a line y and g in Z_m, nb(p0,y,g) = number of NON-BACKTRACKING walks of length
 * 1,3,5,7 from p0 to y whose voltage sum is g; cum(p0,y,g) = sum of nb over these lengths.
 * cum = 0 for some (p0,y,g) is exactly an uncovered triple of hexeval (same sources): the zero count reproduces
 * hexeval's cost (checked on sources 0..NSRC-1 with NSRC = all points).
 * Within each pair (p0,y): dispersion = Var_g(cum)/Mean_g(cum) (Poisson model: 1). Reported as a weighted sum.
 * usage: wcount HEXBIN SOLFILE [NSRC] [SEED]   (NSRC default all points; else random sample) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: wcount HEXBIN SOLFILE [NSRC] [SEED]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t hd[3];
    if (!f || fread(hd, 4, 3, f) != 3) { fprintf(stderr, "no hex\n"); return 1; }
    int q = hd[0], N = hd[1], Q1 = q + 1, V = 2 * N;
    int32_t *pl = malloc(4L * N * Q1);
    if (fread(pl, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1;
    fclose(f);
    FILE *s = fopen(argv[2], "r"); int qq, J, m, D; long cost; char line[256];
    if (!s || fscanf(s, "%d %d %d %d %ld\n", &qq, &J, &m, &D, &cost) != 5) { fprintf(stderr, "bad sol\n"); return 1; }
    if (!fgets(line, sizeof line, s)) return 1;
    int *sig = malloc(sizeof(int) * J * N), *mv = malloc(sizeof(int) * J * N), *hv = malloc(sizeof(int) * N * Q1);
    for (int i = 0; i < J * N; i++) if (fscanf(s, "%d", &sig[i]) != 1) return 1;
    for (int i = 0; i < J * N; i++) if (fscanf(s, "%d", &mv[i]) != 1) return 1;
    for (int i = 0; i < N * Q1; i++) if (fscanf(s, "%d", &hv[i]) != 1) return 1;
    fclose(s);
    int Dg = Q1 + J; long A = (long)V * Dg;
    int *inn = malloc(sizeof(int) * A), *inw = malloc(sizeof(int) * A), *inE = malloc(sizeof(int) * A), *cnt = calloc(V, sizeof(int));
    int NFL = N * Q1;
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k], w = hv[l * Q1 + k];
        inn[(N + l) * Dg + cnt[N + l]] = p; inw[(N + l) * Dg + cnt[N + l]] = w; inE[(N + l) * Dg + cnt[N + l]] = l * Q1 + k; cnt[N + l]++;
        inn[p * Dg + cnt[p]] = N + l; inw[p * Dg + cnt[p]] = (m - w) % m; inE[p * Dg + cnt[p]] = l * Q1 + k; cnt[p]++;
    }
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) {
        int l = sig[t * N + p], w = mv[t * N + p];
        inn[(N + l) * Dg + cnt[N + l]] = p; inw[(N + l) * Dg + cnt[N + l]] = w; inE[(N + l) * Dg + cnt[N + l]] = NFL + t * N + p; cnt[N + l]++;
        inn[p * Dg + cnt[p]] = N + l; inw[p * Dg + cnt[p]] = (m - w) % m; inE[p * Dg + cnt[p]] = NFL + t * N + p; cnt[p]++;
    }
    /* out-arcs of v: arc id b = x*Dg+j means arc inn[b] -> x with voltage inw[b] */
    int *outs = malloc(sizeof(int) * A), *ocnt = calloc(V, sizeof(int));
    for (long b = 0; b < A; b++) { int v = inn[b]; outs[v * Dg + ocnt[v]++] = (int)b; }
    int nsrc = argc > 3 ? atoi(argv[3]) : N; if (nsrc > N) nsrc = N;
    srand(argc > 4 ? atoi(argv[4]) : 1);
    double *cur = calloc((size_t)A * m, sizeof(double)), *nxt = calloc((size_t)A * m, sizeof(double));
    double *cum = calloc((size_t)N * m, sizeof(double));       /* cum[y*m+g] over lengths 1,3,5,7 */
    double sumvar = 0, summu = 0; long zeros = 0; double minsum = 0; long pairs = 0;
    for (int si = 0; si < nsrc; si++) {
        int p0 = nsrc == N ? si : (int)(((long)rand() * N) / ((long)RAND_MAX + 1));
        memset(cur, 0, sizeof(double) * A * m); memset(cum, 0, sizeof(double) * N * m);
        for (int j = 0; j < Dg; j++) { long b = (long)outs[p0 * Dg + j]; cur[b * m + inw[b]] += 1.0; }
        /* arcs with head y: a = y*Dg + j (in-arcs of line y, i.e. arcs p -> y) */
        for (int len = 1; len <= 7; len++) {
            if (len % 2 == 1) for (int y = N; y < V; y++) for (int j = 0; j < Dg; j++) {
                long a = (long)y * Dg + j;
                for (int g = 0; g < m; g++) cum[(size_t)(y - N) * m + g] += cur[a * m + g];
            }
            if (len == 7) break;
            memset(nxt, 0, sizeof(double) * A * m);
            for (long a = 0; a < A; a++) {
                int u = inn[a], v = (int)(a / Dg);
                const double *cv = cur + a * m; int any = 0;
                for (int g = 0; g < m; g++) if (cv[g] != 0) { any = 1; break; }
                if (!any) continue;
                for (int jj = 0; jj < Dg; jj++) {
                    long b = outs[v * Dg + jj]; int x = (int)(b / Dg);
                    if (inE[b] == inE[a]) continue;                                /* no backtracking along the same edge */
                    int w = inw[b]; double *out = nxt + b * m;
                    for (int g = 0; g < m; g++) { int h = g + w; if (h >= m) h -= m; out[h] += cv[g]; }
                }
            }
            double *tmp = cur; cur = nxt; nxt = tmp;
        }
        for (int y = 0; y < N; y++) {
            double mu = 0, m2 = 0, mn = 1e300;
            for (int g = 0; g < m; g++) { double c = cum[(size_t)y * m + g]; mu += c; m2 += c * c; if (c < 0.5) zeros++; if (c < mn) mn = c; }
            mu /= m; m2 /= m; double var = m2 - mu * mu;
            sumvar += var; summu += mu; pairs++; minsum += mn;
        }
    }
    printf("q=%d m=%d J=%d sources=%d uncovered(cum=0)=%ld mean_per_pair=%.2f within_pair_dispersion=%.4f avg_min_over_g=%.3f\n",
           q, m, J, nsrc, zeros, summu / pairs, sumvar / summu, minsum / pairs);
    return 0;
}

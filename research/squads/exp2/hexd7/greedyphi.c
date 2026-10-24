/* Initial bijection phi for plus2 (C port of plus2.py's greedy construction, fast for q = 9).
   p = 0, L0 = the first line through p. Greedy covers:
     C_A: lines at distance 5 from p and 6 from L0, covering the points opposite p (A),
     C_B: points at distance 5 from L0 and 6 from p, blocking the lines opposite L0 (B),
   truncated to |B4| - 1 each; phi maps B4(p)-{p} onto C_A + fillers, C_B + fillers onto B4(L0)-{L0}, rest random.
   Usage: greedyphi HFILE seed OUT.phi   (prints p, L0 and the cover sizes) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int P, q, K, *PL, *LP;
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void bfs(int s, int *d, int *qu) {
    int h = 0, t = 0; for (int i = 0; i < 2 * P; i++) d[i] = -1; d[s] = 0; qu[t++] = s;
    while (h < t) { int v = qu[h++];
        if (v < P) { for (int i = 0; i < K; i++) { int w = P + LP[v * K + i]; if (d[w] < 0) { d[w] = d[v] + 1; qu[t++] = w; } } }
        else { for (int i = 0; i < K; i++) { int w = PL[(v - P) * K + i]; if (d[w] < 0) { d[w] = d[v] + 1; qu[t++] = w; } } } }
}
/* greedy cover: candidates c (n of them) each listing its targets via tg(c, j); target ids 0..T-1; returns count */
static int greedy(int ncand, const int *cand, int per, const int *ctg, int T, const char *istarget, int *out, int maxout) {
    char *cov = calloc(T, 1); int *gain = malloc(sizeof(int) * ncand), nout = 0;
    /* target -> candidates incidence */
    int *deg = calloc(T, sizeof(int)); for (int c = 0; c < ncand; c++) for (int j = 0; j < per; j++) { int t = ctg[c * per + j]; if (t >= 0) deg[t]++; }
    int *st = calloc(T + 1, sizeof(int)); for (int t = 0; t < T; t++) st[t + 1] = st[t] + deg[t];
    int *inc = malloc(sizeof(int) * (st[T] + 1)), *pos = calloc(T, sizeof(int));
    for (int c = 0; c < ncand; c++) for (int j = 0; j < per; j++) { int t = ctg[c * per + j]; if (t >= 0) inc[st[t] + pos[t]++] = c; }
    int left = 0; for (int t = 0; t < T; t++) if (istarget[t]) left++;
    char *used = calloc(ncand, 1);
    for (int c = 0; c < ncand; c++) { gain[c] = 0; for (int j = 0; j < per; j++) { int t = ctg[c * per + j]; if (t >= 0 && istarget[t]) gain[c]++; } }
    while (left > 0) {
        int bg = 0; for (int c = 0; c < ncand; c++) if (!used[c] && gain[c] > bg) bg = gain[c];
        if (bg == 0) break;
        /* random candidate among those with the best gain */
        int cntb = 0; for (int c = 0; c < ncand; c++) if (!used[c] && gain[c] == bg) cntb++;
        int pick = rnd() % cntb, c0 = -1; for (int c = 0; c < ncand; c++) if (!used[c] && gain[c] == bg) { if (pick-- == 0) { c0 = c; break; } }
        used[c0] = 1; if (nout < maxout) out[nout] = cand[c0]; nout++;
        for (int j = 0; j < per; j++) { int t = ctg[c0 * per + j]; if (t < 0 || !istarget[t] || cov[t]) continue; cov[t] = 1; left--;
            for (int k = st[t]; k < st[t + 1]; k++) gain[inc[k]]--; }
    }
    return nout;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: greedyphi HFILE seed OUT.phi\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; K = q + 1;
    PL = malloc(sizeof(int) * P * K); LP = malloc(sizeof(int) * P * K); int *cnt = calloc(P, sizeof(int));
    for (int l = 0; l < P; l++) for (int i = 0; i < K; i++) { int y; if (fscanf(f, "%d", &y) != 1) return 2; PL[l * K + i] = y; LP[y * K + cnt[y]++] = l; }
    fclose(f); rs ^= (unsigned long long)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL;
    int p = 0, L0 = LP[0];
    int *dp = malloc(sizeof(int) * 2 * P), *dL = malloc(sizeof(int) * 2 * P), *qu = malloc(sizeof(int) * 2 * P);
    bfs(p, dp, qu); bfs(P + L0, dL, qu);
    int nB4 = 0; for (int y = 0; y < P; y++) if (dp[y] <= 4 && y != p) nB4++;
    /* (A): candidates = lines with dp = 5, dL = 6; targets = points with dp = 6 */
    int *cA = malloc(sizeof(int) * P), ncA = 0; for (int l = 0; l < P; l++) if (dp[P + l] == 5 && dL[P + l] == 6) cA[ncA++] = l;
    int *tgA = malloc(sizeof(int) * ncA * K); char *isA = calloc(P, 1); for (int y = 0; y < P; y++) if (dp[y] == 6) isA[y] = 1;
    for (int c = 0; c < ncA; c++) for (int j = 0; j < K; j++) tgA[c * K + j] = PL[cA[c] * K + j];
    int *CA = malloc(sizeof(int) * P); int nCA = greedy(ncA, cA, K, tgA, P, isA, CA, P);
    /* (B): candidates = points with dL = 5, dp = 6; targets = lines with dL = 6 */
    int *cB = malloc(sizeof(int) * P), ncB = 0; for (int y = 0; y < P; y++) if (dL[y] == 5 && dp[y] == 6) cB[ncB++] = y;
    int *tgB = malloc(sizeof(int) * ncB * K); char *isB = calloc(P, 1); for (int l = 0; l < P; l++) if (dL[P + l] == 6) isB[l] = 1;
    for (int c = 0; c < ncB; c++) for (int j = 0; j < K; j++) tgB[c * K + j] = LP[cB[c] * K + j];
    int *CB = malloc(sizeof(int) * P); int nCB = greedy(ncB, cB, K, tgB, P, isB, CB, P);
    if (getenv("EXACT")) {   /* exact covers: C_A = lines at distance 5 from p and 4 from L1 (another line through p),
                                C_B = points at distance 5 from L0 and 4 from p1 (another point on L0) */
        int L1 = LP[1], p1 = PL[L0 * K + (PL[L0 * K] == p ? 1 : 0)];
        int *d1 = malloc(sizeof(int) * 2 * P), *e1 = malloc(sizeof(int) * 2 * P);
        bfs(P + L1, d1, qu); bfs(p1, e1, qu);
        nCA = 0; for (int l = 0; l < P; l++) if (dp[P + l] == 5 && d1[P + l] == 4) CA[nCA++] = l;
        nCB = 0; for (int y = 0; y < P; y++) if (dL[y] == 5 && e1[y] == 4) CB[nCB++] = y;
        /* check: every point opposite p on exactly one C_A line, every line opposite L0 through exactly one C_B point */
        int *cov = calloc(P, sizeof(int)), bad = 0;
        for (int i = 0; i < nCA; i++) { if (dL[P + CA[i]] <= 4) bad++; for (int j = 0; j < K; j++) cov[PL[CA[i] * K + j]]++; }
        for (int y = 0; y < P; y++) if (dp[y] == 6 && cov[y] != 1) bad++;
        memset(cov, 0, sizeof(int) * P);
        for (int i = 0; i < nCB; i++) { if (dp[CB[i]] <= 4) bad++; for (int j = 0; j < K; j++) cov[LP[CB[i] * K + j]]++; }
        for (int l = 0; l < P; l++) if (dL[P + l] == 6 && cov[l] != 1) bad++;
        fprintf(stderr, "EXACT: L1=%d p1=%d |C_A|=%d |C_B|=%d (q^4=%d), violations of exactness/disjointness: %d\n", L1, p1, nCA, nCB, q * q * q * q, bad);
    }
    fprintf(stderr, "q=%d P=%d p=%d L0=%d |B4|-1=%d cover sizes |C_A|=%d |C_B|=%d (truncated to %d)\n", q, P, p, L0, nB4, nCA, nCB, nB4);
    if (nCA > nB4) nCA = nB4; if (nCB > nB4) nCB = nB4;
    int *phi = malloc(sizeof(int) * P); for (int y = 0; y < P; y++) phi[y] = -1; phi[p] = L0;
    char *usedL = calloc(P, 1); usedL[L0] = 1;
    /* B4(p)-{p} -> C_A + fillers (not in B4(L0)) */
    int *ys = malloc(sizeof(int) * P), ny = 0; for (int y = 0; y < P; y++) if (dp[y] <= 4 && y != p) ys[ny++] = y;
    for (int i = ny - 1; i > 0; i--) { int j = rnd() % (i + 1), t = ys[i]; ys[i] = ys[j]; ys[j] = t; }
    int k = 0; for (int i = 0; i < nCA; i++) { phi[ys[k++]] = CA[i]; usedL[CA[i]] = 1; }
    int *fl = malloc(sizeof(int) * P), nfl = 0; for (int l = 0; l < P; l++) if (!usedL[l] && dL[P + l] > 4) fl[nfl++] = l;
    for (int i = nfl - 1; i > 0; i--) { int j = rnd() % (i + 1), t = fl[i]; fl[i] = fl[j]; fl[j] = t; }
    for (int i = 0; k < ny; i++) { phi[ys[k++]] = fl[i]; usedL[fl[i]] = 1; }
    /* C_B + filler points (not in B4(p)) -> B4(L0)-{L0} */
    int *ms = malloc(sizeof(int) * P), nm = 0; for (int l = 0; l < P; l++) if (dL[P + l] <= 4 && l != L0) ms[nm++] = l;
    for (int i = nm - 1; i > 0; i--) { int j = rnd() % (i + 1), t = ms[i]; ms[i] = ms[j]; ms[j] = t; }
    char *usedP = calloc(P, 1); for (int y = 0; y < P; y++) if (phi[y] >= 0) usedP[y] = 1;
    k = 0; for (int i = 0; i < nCB && k < nm; i++) if (!usedP[CB[i]]) { phi[CB[i]] = ms[k++]; usedP[CB[i]] = 1; }
    int *fp = malloc(sizeof(int) * P), nfp = 0; for (int y = 0; y < P; y++) if (!usedP[y]) fp[nfp++] = y;
    for (int i = nfp - 1; i > 0; i--) { int j = rnd() % (i + 1), t = fp[i]; fp[i] = fp[j]; fp[j] = t; }
    int fi = 0; while (k < nm) { phi[fp[fi]] = ms[k++]; usedP[fp[fi]] = 1; fi++; }
    for (int i = 0; i < nm; i++) usedL[ms[i]] = 1;
    /* rest */
    int *rl = malloc(sizeof(int) * P), nrl = 0; for (int l = 0; l < P; l++) if (!usedL[l]) rl[nrl++] = l;
    for (int i = nrl - 1; i > 0; i--) { int j = rnd() % (i + 1), t = rl[i]; rl[i] = rl[j]; rl[j] = t; }
    k = 0; for (int y = 0; y < P; y++) if (phi[y] < 0) phi[y] = rl[k++];
    /* sanity: bijection */
    char *seen = calloc(P, 1); for (int y = 0; y < P; y++) { if (phi[y] < 0 || seen[phi[y]]) { fprintf(stderr, "not a bijection\n"); return 1; } seen[phi[y]] = 1; }
    f = fopen(argv[3], "w"); for (int y = 0; y < P; y++) fprintf(f, "%d%c", phi[y], y + 1 < P ? ' ' : '\n'); fclose(f);
    printf("p=%d L0=%d\n", p, L0);
    return 0;
}

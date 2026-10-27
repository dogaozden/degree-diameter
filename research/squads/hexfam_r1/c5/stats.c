#include "/home/user/degree-diameter/research/projects/hexagon-family/tools/q6.h"
int main(int argc, char **argv) {
    Hex h = hex_load(argv[1]); int Q = h.q, N = h.N; int *ids; int n = read_ids(argv[2], &ids);
    int *tight = calloc(N, sizeof(int)); char *in = calloc(N, 1);
    for (int i = 0; i < n; i++) in[ids[i]] = 1;
    for (int i = 0; i < n; i++) for (int x = 0; x < N; x++) if (Bxy(h.C + 7*(size_t)x, h.C + 7*(size_t)ids[i]) == 0) tight[x]++;
    /* tight[x] counts ids[i]==x too (B(x,x)=0), so subtract for members */
    long cnt[64] = {0}; int mn = 1 << 30, mx = 0;
    for (int x = 0; x < N; x++) { if (in[x]) { tight[x] = -1; continue; } int t = tight[x]; if (t < mn) mn = t; if (t > mx) mx = t; if (t < 64) cnt[t]++; }
    printf("q=%d |S|=%d min tight=%d max tight=%d\n", Q, n, mn, mx);
    for (int t = 0; t < 64; t++) if (cnt[t]) printf("tight %d: %ld\n", t, cnt[t]);
    return 0;
}

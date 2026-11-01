static i64 cost(void) {
    for (int i = 0; i < d; i++) SI[i] = inv(S[i]);
    if (D % 2 == 0) { lastA = N - ball(0); lastB = 0; return lastA; }
    lastA = N - ball(0); lastB = N - ball(1); return lastA + lastB;
}
static void writesol(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %d meta %lld %lld %lld n 1 N %lld\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N);
    for (int i = 0; i < d; i++) fprintf(f, "%lld meta(a=%lld,j=%lld) z=0\n", (long long)(S[i].a * K_ + S[i].j), (long long)S[i].a, (long long)S[i].j);
    fclose(f);
}
static int readsol(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0; char line[512]; if (!fgets(line, sizeof line, f)) return 0;
    int n = 0; long long a, j;
    while (n < d && fgets(line, sizeof line, f)) { char *p = strstr(line, "meta(a="); if (!p) continue;
        if (sscanf(p, "meta(a=%lld,j=%lld)", &a, &j) == 2) { S[n].a = a % M; S[n].j = j % K_; n++; } }
    fclose(f); return n == d;
}

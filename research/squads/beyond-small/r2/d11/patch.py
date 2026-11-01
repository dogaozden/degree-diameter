import re
src = open('hubpack2.c').read()
def rep(old, new, count=1):
    global src
    assert src.count(old) == count, (src.count(old), old[:70])
    src = src.replace(old, new)

rep('#define H 16896\n', '#define H 16896\n#define ADJ(a,b) ((C[(size_t)(a)*CW+((b)>>6)]>>((b)&63))&1)\n')
rep('    int (*cand)[17] = malloc(sizeof(int[17]) * NC), *csz = malloc(4 * NC); int nc = 0; long tries = 0;\n',
'''    const char *stpath = argc > 7 ? argv[7] : NULL;
    int warm = 0, nc = 0, nbinit = 0; int (*cand)[17]; int *csz; long tries = 0; int *bestinit = NULL;
    FILE *sf = stpath ? fopen(stpath, "r") : NULL;
    if (sf) {
        if (fscanf(sf, "%d", &nc) != 1) nc = 0;
        cand = malloc(sizeof(int[17]) * (nc + 1)); csz = malloc(4 * (nc + 1));
        for (int i = 0; i < nc; i++) { if (fscanf(sf, "%d", &csz[i]) != 1) return 4; for (int k = 0; k < csz[i]; k++) if (fscanf(sf, "%d", &cand[i][k]) != 1) return 4; }
        if (fscanf(sf, "%d", &nbinit) != 1) nbinit = 0;
        bestinit = malloc(4 * (nbinit + 1)); for (int a = 0; a < nbinit; a++) if (fscanf(sf, "%d", &bestinit[a]) != 1) return 4;
        fclose(sf); warm = nc > 0;
        fprintf(stderr, "state: %d candidates, saved packing %d\\n", nc, nbinit);
    } else { cand = malloc(sizeof(int[17]) * NC); csz = malloc(4 * NC); }
''')
rep('    while (nc < NC && now() - t0 < secs * 0.5) {\n', '    while (!warm && nc < NC && now() - t0 < secs * 0.5) {\n')
# warm start + kicks in the clique search
rep('''    int *cnt = calloc(nc, 4);   /* cnt[v] = number of current members v is NOT adjacent to */
    while (now() - t0 < secs) {
        ncur = 0; memset(inc, 0, 4 * nc);
        for (int i = 0; i < nc; i++) cnt[i] = 0;
''', '''    int *cnt = calloc(nc, 4);   /* cnt[v] = number of current members v is NOT adjacent to */
    int first = warm;
    while (now() - t0 < secs) {
        ncur = 0; memset(inc, 0, 4 * nc);
        for (int i = 0; i < nc; i++) cnt[i] = 0;
        if (first) {   /* warm start: resume from the saved packing */
            first = 0; nbest = nbinit; memcpy(best, bestinit, 4 * nbinit);
            for (int a = 0; a < nbinit; a++) { int v = bestinit[a]; inc[v] = 1; cur[ncur++] = v; }
            for (int a = 0; a < ncur; a++) for (int x = 0; x < nc; x++) if (x != cur[a] && !ADJ(cur[a], x)) cnt[x]++;
        }
''')
rep('''            if (x < 0) break;
''', '''            if (x < 0) {   /* stuck: kick = swap a random member for a random low-conflict outsider */
                int a = rnd() % ncur; int m = cur[a]; inc[m] = 0; cur[a] = cur[--ncur];
                for (int y = 0; y < nc; y++) if (y != m && !ADJ(m, y)) cnt[y]--;
                int bx = -1, bc = 1 << 30;
                for (int s = 0; s < 50; s++) { int y = rnd() % nc; if (!inc[y] && y != m && cnt[y] < bc) { bc = cnt[y]; bx = y; } }
                if (bx < 0) bx = m;
                inc[bx] = 1; cur[ncur++] = bx;
                for (int y = 0; y < nc; y++) if (y != bx && !ADJ(bx, y)) cnt[y]++;
                continue;
            }
''')
rep('''    FILE *g = fopen(argv[6], "w");
''', '''    if (stpath) {   /* save candidates and best packing for the next chained run */
        char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", stpath);
        FILE *o = fopen(tmp, "w"); fprintf(o, "%d\\n", nc);
        for (int i = 0; i < nc; i++) { fprintf(o, "%d", csz[i]); for (int k = 0; k < csz[i]; k++) fprintf(o, " %d", cand[i][k]); fprintf(o, "\\n"); }
        fprintf(o, "%d", nbest); for (int a = 0; a < nbest; a++) fprintf(o, " %d", best[a]); fprintf(o, "\\n"); fclose(o);
        rename(tmp, stpath);
    }
    FILE *g = fopen(argv[6], "w");
''')
open('hubpack2.c', 'w').write(src)
print("ok")

src = open('hubpack2.c').read()
def rep(old, new):
    global src
    assert src.count(old) == 1, (src.count(old), old[:80])
    src = src.replace(old, new)
rep('''    int first = warm;
''', '''    int first = warm; long gr = 0; long *tabu = calloc(nc, 8);
''')
rep('''        for (int rounds = 0; rounds < 20000 && now() - t0 < secs; rounds++) {
            int added = 0;
            for (int x = 0; x < nc; x++) if (!inc[x] && cnt[x] == 0) {''',
'''        for (int rounds = 0; rounds < 20000 && now() - t0 < secs; rounds++) {
            int added = 0; gr++;
            for (int x = 0; x < nc; x++) if (!inc[x] && cnt[x] == 0 && tabu[x] <= gr) {''')
rep('''int x = -1; for (int s = 0; s < 200; s++) { int y = rnd() % nc; if (!inc[y] && cnt[y] == 1) { x = y; break; } }''',
'''int x = -1; for (int s = 0; s < 200; s++) { int y = rnd() % nc; if (!inc[y] && cnt[y] == 1 && tabu[y] <= gr) { x = y; break; } }''')
i = src.index('            if (x < 0) {   /* stuck: kick')
j = src.index('            int drop = -1;', i)
src = src[:i] + '''            if (x < 0) {   /* stuck: kick = drop a random member, which is tabu for a while */
                int a = rnd() % ncur; int m = cur[a]; inc[m] = 0; cur[a] = cur[--ncur];
                for (int y = 0; y < nc; y++) if (y != m && !ADJ(m, y)) cnt[y]--;
                tabu[m] = gr + 50;
                continue;
            }
''' + src[j:]
rep('''            int m = cur[drop]; inc[m] = 0; cur[drop] = cur[--ncur];''',
'''            int m = cur[drop]; inc[m] = 0; cur[drop] = cur[--ncur]; tabu[m] = gr + 7;''')
rep('''    if (stpath) {   /* save''', '''    /* independent check of the packing: pairwise compatible and vertex-disjoint */
    { static char used[H]; for (int a = 0; a < nbest; a++) { for (int k = 0; k < csz[best[a]]; k++) { int t = cand[best[a]][k]; if (used[t]) { fprintf(stderr, "BUG: shared vertex\\n"); return 5; } used[t] = 1; }
        for (int b = a + 1; b < nbest; b++) if (!ADJ(best[a], best[b])) { fprintf(stderr, "BUG: not a clique\\n"); return 5; } }
      fprintf(stderr, "packing check OK: %d hubs pairwise compatible and disjoint\\n", nbest); }
    if (stpath) {   /* save''')
open('hubpack2.c', 'w').write(src)
print('ok')

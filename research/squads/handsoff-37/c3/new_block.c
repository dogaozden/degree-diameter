/* score of a child: collisions it adds (state restored afterwards); BIG if the child is pruned */
static long score_edge(int x, int y, int tx) {
    int s = side_[x]; int vt = cheap_ok(x, y, tx); if (vt < 0) return -1;
    int was = anynz; add_edge(s == 0 ? x : y, s == 0 ? y : x, vt); if (vt) anynz = 1;
    long mark = lsp; long c0 = coll_total; int ok = check_new_edge(); long d = coll_total - c0;
    undo_to(mark); del_edge(); anynz = was;
    return ok ? d : 1000000L;
}
static long score_newvertex(int x, int o, int s) {
    int y = nv++; side_[y] = o; deg_[y] = 0; nside[o]++; seen_[y][y][0] |= 1ULL;
    add_edge(s == 0 ? x : y, s == 0 ? y : x, 0);
    long mark = lsp; long c0 = coll_total; int ok = check_new_edge(); long d = coll_total - c0;
    undo_to(mark); del_edge(); seen_[y][y][0] &= ~1ULL; nv--; nside[o]--;
    return ok ? d : 1000000L;
}
/* order children: random shuffle, then (heur > 0) stable sort by score + noise */
static void order_children(Ch *c, int nc) {
    shuffle(c, nc);
    if (heur == 0) return;
    for (int i = 1; i < nc; i++) { Ch v = c[i]; int j = i - 1;
        while (j >= 0 && c[j].sc > v.sc) { c[j + 1] = c[j]; j--; }
        c[j + 1] = v; }
}
static void fill_node(int x, int minkey) {
    if (aborted) return;
    nodes++; if (nodes > budget) { aborted = 1; return; }
    if (ne > maxne) maxne = ne; hist_ne[ne]++;
    if (deg_[x] == 3) { next_vertex(); return; }
    int s = side_[x], o = 1 - s;
    Ch c[160]; int nc = 0;
    if (minkey < BIG) for (int y = x + 1; y < nv; y++) {
        if (side_[y] != o || deg_[y] >= 3) continue;
        for (int t = 0; t < p; t++) {
            int key = y * p + t; if (key < minkey) continue;
            if (cheap_ok(x, y, t) < 0) continue;
            c[nc].type = 0; c[nc].y = y; c[nc].t = t; c[nc].sc = 0; nc++;
        }
    }
    if (nv < 2 * k && nside[o] < k) { c[nc].type = 1; c[nc].y = 0; c[nc].t = 0; c[nc].sc = 0; nc++; }
    if (heur) for (int i = 0; i < nc; i++) {
        long sc = (c[i].type == 0) ? score_edge(x, c[i].y, c[i].t) : score_newvertex(x, o, s);
        c[i].sc = sc * 16 + (heur == 2 ? (long)(rnd() % 16) : 0);
    }
    order_children(c, nc);
    for (int i = 0; i < nc && !aborted; i++) {
        if (c[i].type == 0) {
            int y = c[i].y, t = c[i].t;
            int was = anynz; int vt = cheap_ok(x, y, t); if (vt < 0) continue;
            add_edge(s == 0 ? x : y, s == 0 ? y : x, vt);
            if (vt) anynz = 1;
            long mark = lsp;
            if (check_new_edge()) fill_node(x, y * p + t + 1);
            undo_to(mark); del_edge(); anynz = was;
        } else {
            int y = nv++; side_[y] = o; deg_[y] = 0; nside[o]++;
            seen_[y][y][0] |= 1ULL;
            add_edge(s == 0 ? x : y, s == 0 ? y : x, 0);
            long mark = lsp;
            if (check_new_edge()) par_node(x, y, 0);
            undo_to(mark); del_edge();
            seen_[y][y][0] &= ~1ULL; nv--; nside[o]--;
        }
    }
}

/* after a new vertex y: stop adding parallel edges x-y (rest of x's edges go to new vertices), or add a parallel
   edge with voltage t > lastt */
static void par_node(int x, int y, int lastt) {
    if (aborted) return;
    Ch c[160]; int nc = 0;
    c[nc].type = 2; c[nc].sc = 0; nc++;
    if (deg_[x] < 3 && deg_[y] < 3) for (int t = lastt + 1; t < p; t++) { c[nc].type = 3; c[nc].t = t; c[nc].y = y; c[nc].sc = 0; nc++; }
    if (heur) for (int i = 0; i < nc; i++) if (c[i].type == 3) {
        long sc = score_edge(x, y, c[i].t); c[i].sc = sc * 16 + (heur == 2 ? (long)(rnd() % 16) : 0); }
    order_children(c, nc);
    for (int i = 0; i < nc && !aborted; i++) {
        if (c[i].type == 2) { fill_node(x, BIG); }
        else {
            int t = c[i].t;
            int was = anynz; int vt = cheap_ok(x, y, t); if (vt < 0) continue;
            add_edge(side_[x] == 0 ? x : y, side_[x] == 0 ? y : x, vt);
            if (vt) anynz = 1;
            long mark = lsp;
            if (check_new_edge()) par_node(x, y, t);
            undo_to(mark); del_edge(); anynz = was;
        }
    }
}


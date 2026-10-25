"""exact max-weight clique (bitset B&B with weighted greedy colouring bound). adj: list of python int bitsets."""
import time
def max_weight_clique(w, adj, tlimit=60.0):
    n = len(w)
    best = [0, 0]  # weight, bitset
    t0 = time.time()
    order = sorted(range(n), key=lambda i: -w[i])
    pos = {v: k for k, v in enumerate(order)}
    # re-index so that vertex k in order
    W = [w[v] for v in order]
    A = [0] * n
    for a_new, a in enumerate(order):
        bits = 0
        for b_new, b in enumerate(order):
            if (adj[a] >> b) & 1: bits |= (1 << b_new)
        A[a_new] = bits
    timed_out = [False]
    def colour_bound(cand):
        # greedy colouring of candidate set in the order of index (desc weight); returns list of (vertex, colour class bound)
        rem = cand; bound = 0; classes = []
        while rem:
            cls = 0; avail = rem; mx = 0
            while avail:
                v = (avail & -avail).bit_length() - 1
                cls |= 1 << v; mx = max(mx, W[v]) if mx == 0 else mx
                avail &= ~A[v] & ~(1 << v)
                rem &= ~(1 << v)
            bound += W[(cls & -cls).bit_length() - 1]  # first vertex has max weight (sorted)
        return bound
    def expand(cur_w, cur_set, cand):
        if time.time() - t0 > tlimit: timed_out[0] = True; return
        if cur_w > best[0]: best[0] = cur_w; best[1] = cur_set
        if not cand: return
        if cur_w + colour_bound(cand) <= best[0]: return
        # branch on vertices in cand (highest weight first)
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            if cur_w + sum_w(c) <= best[0]: return
            expand(cur_w + W[v], cur_set | (1 << v), c & A[v])
            c &= ~(1 << v)
            if timed_out[0]: return
    def sum_w(bits):
        s = 0
        while bits:
            v = (bits & -bits).bit_length() - 1; s += W[v]; bits &= bits - 1
        return s
    expand(0, 0, (1 << n) - 1)
    verts = [order[v] for v in range(n) if (best[1] >> v) & 1]
    return best[0], verts, not timed_out[0]

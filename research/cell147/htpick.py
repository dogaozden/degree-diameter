"""Pick hop voltages h_1..h_j in Z_m: 0, +-h_t distinct; maximize the minimum weighted number of 2-hop route types
reaching each element not covered by single hops (PL routes weigh 2, PP/LL/LP routes 1). Prints the best HT."""
import itertools, random, sys
def score(h, m):
    single = {0} | {x % m for x in h} | {(-x) % m for x in h}
    if len(single) != 2 * len(h) + 1: return None
    w = [0] * m
    j = len(h)
    for a in range(j):
        for b in range(j):
            w[(h[a] + h[b]) % m] += 1          # PP
            w[(-h[a] - h[b]) % m] += 1         # LL
            if a != b:
                w[(h[a] - h[b]) % m] += 2      # PL
                w[(-h[a] + h[b]) % m] += 1     # LP
    extra = [g for g in range(m) if g not in single]
    if not extra: return (99, 0)
    return (min(w[g] for g in extra), sum(w[g] for g in extra) / len(extra))
def best(m, j, tries=20000, seed=1):
    rng = random.Random(seed); bestv = None; bh = None
    cand = list(range(1, m))
    if j <= 3 and m <= 64:
        it = itertools.combinations(range(1, m), j)
    else:
        it = (sorted(rng.sample(cand, j)) for _ in range(tries))
    for h in it:
        s = score(list(h), m)
        if s is None: continue
        if bestv is None or s > bestv: bestv, bh = s, h
    return bh, bestv
if __name__ == "__main__":
    m, j = int(sys.argv[1]), int(sys.argv[2])
    h, s = best(m, j)
    print(" ".join(map(str, h)), s)

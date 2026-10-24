"""Base file for a Z_5 x Z_k lift of H(q) + two hop matchings (liftdiam format), card c3.

Hop 1 at point p goes to line s1[p] with Z_5 voltage 1, hop 2 to s2[p] with Z_5 voltage 2 (polygon cover).
s1, s2 are disjoint, non-incident permutations (points -> lines), so the base stays simple.
Flags carry voltage 0. Hop labels are uniform random in Z_k (the starting point of the annealing).

usage: python3 -B gen_base.py q k seed out.txt
"""
import random
import sys

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402


def repair_perm(N, forbid, rng):
    """random permutation sigma of range(N) with sigma[p] not in forbid[p]"""
    perm = list(range(N))
    rng.shuffle(perm)
    bad = {p for p in range(N) if perm[p] in forbid[p]}
    tries = 0
    while bad:
        tries += 1
        if tries > 10 ** 6:
            raise RuntimeError('no admissible permutation found')
        p = rng.choice(tuple(bad))
        p2 = rng.randrange(N)
        if p2 == p:
            continue
        if perm[p2] not in forbid[p] and perm[p] not in forbid[p2]:
            perm[p], perm[p2] = perm[p2], perm[p]
            for x in (p, p2):
                if perm[x] in forbid[x]:
                    bad.add(x)
                else:
                    bad.discard(x)
    return perm


def main():
    q, k, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    H = gh.load(q)
    N = H.N
    rng = random.Random(seed)
    inc = [set(int(L) for L in H.through[p]) for p in range(N)]
    s1 = repair_perm(N, inc, rng)
    s2 = repair_perm(N, [inc[p] | {s1[p]} for p in range(N)], rng)
    edges = [(p, L, 0, 0) for (p, L) in gh.flags(H)]
    for p in range(N):
        edges.append((p, N + s1[p], 1, rng.randrange(k)))
        edges.append((p, N + s2[p], 2, rng.randrange(k)))
    gh.write_base(out, 2 * N, 5, k, edges)
    print(f'wrote {out}: q={q} N={N} M=5x{k} edges={len(edges)}')


if __name__ == '__main__':
    main()

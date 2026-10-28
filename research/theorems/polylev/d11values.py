"""d11values.py: first values at (Delta, 11) from certified K per q (Corollaries 5.2 / 5.5 of POLYGON_LEVELS.md).
Order 2N(q)(2rK+1), degree q+1+r. Prints, for every Delta, the best (q, r) among the certified K and the share of the
bipartite Moore bound. Usage: python3 d11values.py q:K [q:K ...]"""
import sys


def moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


def main():
    Ks = {}
    for a in sys.argv[1:]:
        q, K = a.split(':')
        Ks[int(q)] = int(K)
    print('| (Delta, 11) | q | r | K | order | % of Moore bound |')
    print('|---|---:|---:|---:|---:|---:|')
    for d in range(3, 21):
        best = None
        for q, K in Ks.items():
            r = d - q - 1
            if r < 1:
                continue
            N = (q ** 6 - 1) // (q - 1)
            order = 2 * N * (2 * r * K + 1)
            if best is None or order > best[0]:
                best = (order, q, r, K)
        if best:
            o, q, r, K = best
            print(f'| ({d}, 11) | {q} | {r} | {K:,} | {o:,} | {100 * o / moore(d, 11):.2f} |')


if __name__ == '__main__':
    main()

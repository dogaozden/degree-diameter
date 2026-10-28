"""sizes.py: orders of the ball lifts of H(q) against the lab's current values (tables for POLYGON_LEVELS.md).
2N = 2(q^6-1)/(q-1) is the order of the incidence graph of H(q).
D = 9:  2N (2 r k + 1), Delta = q+1+r, k = number of balanced 2-ball classes (k <= q^2+q+1).
D = 10: 2N (2 r' (q^3+1) + 1), Delta = q+1+2r' (spread stars, every q).
D = 11: 2N (2 r K + 1), Delta = q+1+r, K = disjoint lines / non-collinear points (K <= q^4+q^2+1).
Usage: python3 sizes.py [D]"""
import sys

LAB = {
    8: {3: 288, 4: 2184, 5: 9760, 6: 31680, 7: 95760, 8: 239904, 9: 546720, 10: 1176480, 11: 2258520, 12: 4650100,
        13: 6999552, 14: 14172480, 15: 18128880, 16: 36201060, 17: 41373072, 18: 57637680, 19: 86317296,
        20: 122739120},
    9: {3: 506, 4: 4970, 5: 29756, 6: 127296, 7: 462840, 8: 1341600, 9: 3499776, 10: 8003856, 11: 16792080,
        12: 34026720, 13: 67742688, 14: 116068656, 15: 208029120, 16: 337394400, 17: 501707400, 18: 790626816,
        19: 1218394320, 20: 1823175864},
    10: {3: 810, 4: 12416, 5: 95472, 6: 524160, 7: 2298240, 8: 8043840, 9: 23975280, 10: 60141120, 11: 148729680,
         12: 325832976, 13: 677714400, 14: 1326627120, 15: 2467618800, 16: 4220872800, 17: 7022052336,
         18: 11787972672, 19: 19233722496, 20: 30518778360},
    11: {3: 1474, 4: 19152, 5: 253080, 6: 1971744, 7: 10648176, 8: 43702560, 9: 145258344, 10: 445709568},
}
QS = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19]


def twoN(q):
    return 2 * (q ** 6 - 1) // (q - 1)


def table(D):
    rows = []
    for q in QS:
        for r in range(1, 8):
            d = q + 1 + r
            if d > 20:
                continue
            if D == 9:
                kmax = q * q + q + 1
                m = 2 * r * kmax + 1
            elif D == 10:
                if r % 2:
                    continue
                kmax = q ** 3 + 1
                m = r * kmax + 1
            elif D == 11:
                kmax = q ** 4 + q * q + 1
                m = 2 * r * kmax + 1
            order = twoN(q) * m
            lab = LAB[D].get(d)
            need = None
            if lab is not None:
                # smallest k with 2N(2 r k + 1) > lab  (D = 9, 11); D = 10 has no free parameter
                if D in (9, 11):
                    need = (lab // twoN(q) - 1) // (2 * r) + 1
                    while twoN(q) * (2 * r * need + 1) <= lab:
                        need += 1
            rows.append((d, q, r, kmax, order, lab, need))
    rows.sort()
    return rows


def main():
    Ds = [int(sys.argv[1])] if len(sys.argv) > 1 else [9, 10, 11]
    for D in Ds:
        print(f'\n### D = {D}\n')
        if D == 10:
            print('| Delta | q | matchings 2r\' | K = q^3+1 | order | lab value | ratio |')
            print('|---:|---:|---:|---:|---:|---:|---:|')
            for d, q, r, kmax, order, lab, need in table(D):
                print(f'| {d} | {q} | {r} | {kmax:,} | {order:,} | {lab:,} | {order / lab:.3f} |' if lab else
                      f'| {d} | {q} | {r} | {kmax:,} | {order:,} | - | - |')
        else:
            name = 'k' if D == 9 else 'K'
            print(f'| Delta | q | r | max {name} | order at max {name} | lab value | {name} needed to beat it |')
            print('|---:|---:|---:|---:|---:|---:|---:|')
            for d, q, r, kmax, order, lab, need in table(D):
                labs = f'{lab:,}' if lab else '-'
                ns = (f'{need} ({100 * need / kmax:.0f}%)' if need <= kmax else 'impossible') if need else '-'
                print(f'| {d} | {q} | {r} | {kmax:,} | {order:,} | {labs} | {ns} |')


if __name__ == '__main__':
    main()

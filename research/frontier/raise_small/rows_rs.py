#!/usr/bin/env python3
"""rows_rs.py: replace the BEYOND_TABLE rows of the cells raised by job raise-small-d (run from the repo root).
Each entry: cell -> (value, construction, check). Percent of M_b and the upper bound M_b - 6 are recomputed."""
import re

FILE = 'research/frontier/beyond/BEYOND_TABLE.md'
G = 'research/frontier/beyond/graphs/'
ROWS = {
    (3, 12): (2436, 'regular lift of a 2+2 cubic base multigraph over Z29 x\\|_7 Z21 (order 609), base and voltages '
              'found together by joint annealing (salift_s, director 2+2 scan, job raise-small-d); earlier 2,368 '
              '(4+4 over Z37 x\\|_6 Z8, own-small), 2,176 (metacyclic Haar)',
              f'apsp VALID, diameter exactly 12 ({G}d3D12_n2436_lift2_meta29_21_7.apsp.txt)'),
    (3, 13): (4324, 'regular lift of a 2+2 cubic base multigraph over Z47 x\\|_2 Z23 (order 1,081), joint annealing '
              '(raise-small-d squad r2/d02, first 22-s screen); earlier 3,744 (3+3 over Z13 x\\|_2 Z48, 4+4 over '
              'Z39 x\\|_17 Z12), 3,696, 3,648 (this job), 3,400 (Z170 lift of GP(10,3), beyond-d13); census CAT(3360,4)',
              f'apsp VALID, diameter exactly 13 ({G}d3D13_n4324_lift2_meta47_23_2_d02.apsp.txt)'),
    (3, 14): (7008, 'regular lift of a 3+3 cubic base multigraph over Z73 x\\|_10 Z16 (order 1,168), joint annealing '
              '(raise-small-d squad r2/d03, chaining r1/c06\'s cost-2 state); also 7,004 (2+2 over Z103 x\\|_8 Z17, '
              'r2/d04); earlier 6,600 and 6,528 (this job), 5,706 (Z317 lift of the Pappus graph, beyond-d13); the '
              'Foster census has CSS(6272,7) with 6,272',
              f'apsp VALID, diameter exactly 14 ({G}d3D14_n7008_lift3_meta73_16_10_d03.apsp.txt)'),
    (4, 12): (74118, 'Haar graph of the Frobenius group Z1123 x\\|_60 Z33 (order 37,059), S random (hmeta, '
              'raise-small-d squad r3/e10, a fresh seed; solution research/frontier/sols/d4D12_meta_1123_33_60_e10.txt); '
              'earlier 74,066 (Z1277 x\\|_964 Z29, beyond-d13)',
              'metacheck VALID from (e,A) and (e,B) and apsp VALID, diameter exactly 12 '
              '(research/frontier/raise_small/checks/d4D12_meta_1123_33_60_e10.check.txt)'),
    (4, 13): (193058, 'Haar graph of the odd-order Frobenius group Z1163 x\\|_102 Z83 (order 96,529), S random '
              '(hmeta; director, fresh seed 2006 after squad r3/e10 left it at cost 2; solution '
              'research/frontier/sols/d4D13_meta_1163_83_102_dir.txt); earlier 192,382 (Z2237 x\\|_1984 Z43, beyond-d13)',
              'metacheck VALID from (e,A) and (e,B) and apsp VALID, diameter exactly 13 '
              '(research/frontier/raise_small/checks/d4D13_meta_1163_83_102_dir.check.txt)'),
    (4, 14): (498798, 'Haar graph of the Frobenius group Z3079 x\\|_568 Z81 (order 249,399), S random (hmeta, '
              'raise-small-d squad r1/c15; solution research/frontier/sols/d4D14_meta_3079_81_568_c15.txt); earlier '
              '497,042 (Z2731 x\\|_2400 Z91, beyond-d13)',
              'metacheck VALID from (e,A) and (e,B) and apsp VALID, diameter exactly 14 '
              '(research/frontier/raise_small/checks/d4D14_meta_3079_81_568_c15.check.txt)'),
}


def mb(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


def main():
    txt = open(FILE).read().split('\n')
    for i, line in enumerate(txt):
        m = re.match(r'\| \((\d+),(\d+)\) \|', line)
        if not m: continue
        cell = (int(m.group(1)), int(m.group(2)))
        if cell not in ROWS: continue
        v, cons, chk = ROWS[cell]
        cols = line.split(' | ')
        M = mb(*cell)
        ub = M if cell[1] in (3, 4, 6) else M - 6
        last = cols[-1]
        txt[i] = (f"| ({cell[0]},{cell[1]}) | **{v:,}** | {100 * v / M:.2f} | {ub:,} | {cons} | {chk} | {last}")
        print('row', cell, v)
    open(FILE, 'w').write('\n'.join(txt))


if __name__ == '__main__':
    main()

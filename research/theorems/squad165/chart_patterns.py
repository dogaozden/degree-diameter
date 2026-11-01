"""Write the singular-pattern table of a chart: lines "side i1 i2 i3 i4 rank" for all 216 nonbacktracking colour
patterns (side A: walk from an A-vertex, side B: from a B-vertex), plus the pencil check.
usage: python3 chart_patterns.py chart out.txt"""
import sys, itertools
from lift_check import load_chart, rank
from chart import mat_vec, mat_inv
import chart2
A, b = load_chart(sys.argv[1]); Ai = [mat_inv(M) for M in A]
with open(sys.argv[2], 'w') as f:
    nsing = 0
    for (i1, i2, i3, i4) in itertools.product(range(4), repeat=4):
        if i1 == i2 or i2 == i3 or i3 == i4: continue
        rA = rank([mat_vec(Ai[i2], b[i1]), mat_vec(Ai[i2], b[i2]), mat_vec(Ai[i3], b[i3]), mat_vec(Ai[i3], b[i4])])
        rB = rank([mat_vec(A[i2], mat_vec(Ai[i1], b[i1])), b[i2], b[i3], mat_vec(A[i3], mat_vec(Ai[i4], b[i4]))])
        f.write(f"A {i1} {i2} {i3} {i4} {rA}\nB {i1} {i2} {i3} {i4} {rB}\n")
        nsing += (rA < 4) + (rB < 4)
print('singular patterns', nsing, 'pencil violations', chart2.pencil_violations(A, b))

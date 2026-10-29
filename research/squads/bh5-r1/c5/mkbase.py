import sys
# usage: mkbase.py OUT k "row1" "row2" ...  (k x k multiplicity matrix, rows sum to 5)
out = sys.argv[1]; rows = [list(map(int, r.split(','))) for r in sys.argv[2:]]
k = len(rows); E = []
for i in range(k):
    for j in range(k):
        E += [(i, k + j)] * rows[i][j]
with open(out, 'w') as f:
    f.write(f"{2*k} {len(E)}\n" + " ".join(['0']*k + ['1']*k) + "\n")
    for a, c in E: f.write(f"{a} {c}\n")

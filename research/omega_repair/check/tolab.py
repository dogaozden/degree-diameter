"""Independent check of twist.c's counts with the table audit's builder (omega_model.h / omega_eval.c, branch
claude/table-audit-2-p7x6hn, copied unchanged): write the hexagon as the audit's edge list (points 0..n-1, lines
n..2n-1) and a twisted labelling in the audit's format (P_c[t] = t, L_c[t] = lam_c(t); reading 2 = inner P on a-blocks,
inner L on b-blocks).  usage: tolab.py hex_qQ.txt twists.bin TYPES out_prefix   (prints the INNER string)"""
import sys, numpy as np
f = open(sys.argv[1]); q, n, nl = map(int, f.readline().split())
L = [list(map(int, f.readline().split())) for _ in range(nl)]
with open(sys.argv[4] + '.hex', 'w') as g:
    g.write(f"{2 * n}\n")
    for l, pts in enumerate(L):
        for p in pts:
            g.write(f"{p} {n + l}\n")
raw = np.fromfile(sys.argv[2], dtype=np.int32); C, nn = raw[0], raw[1]; assert nn == n
body = raw[2:].reshape(C, 2, n)
with open(sys.argv[4] + '.lab', 'w') as g:
    for c in range(C): g.write(' '.join(map(str, range(n))) + '\n')
    for c in range(C): g.write(' '.join(map(str, body[c, 1])) + '\n')
types = sys.argv[3]
print(''.join('P' if t == 'a' else 'L' for t in types))

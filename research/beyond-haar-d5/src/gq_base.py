#!/usr/bin/env python3
"""Write a vl base file from W(q): incidence graph (points 0..N-1 side 0, lines N..2N-1 side 1) plus J random perfect
matchings point -> line (MATCH=random) or none.  usage: gq_base.py q J SEED OUT [DOUBLE]
DOUBLE=1 makes the J matchings copies of one matching (parallel edges)."""
import random, struct, sys
q, J, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
double = len(sys.argv) > 5 and sys.argv[5] == '1'
random.seed(seed)
with open(f'gq/gq_q{q}.bin', 'rb') as f:
    qq, N, L = struct.unpack('3i', f.read(12))
    lines = [list(struct.unpack(f'{q+1}i', f.read(4 * (q + 1)))) for _ in range(L)]
E = [(p, N + l) for l in range(L) for p in lines[l]]
sig = list(range(N)); random.shuffle(sig)
for j in range(J):
    if not double and j > 0:
        sig = list(range(N)); random.shuffle(sig)
    E += [(p, N + sig[p]) for p in range(N)]
with open(out, 'w') as f:
    f.write(f"{2 * N} {len(E)}\n" + " ".join(['0'] * N + ['1'] * N) + "\n")
    for u, w in E: f.write(f"{u} {w}\n")
print(f"{out}: b={2*N} E={len(E)} degree={q+1+J}")

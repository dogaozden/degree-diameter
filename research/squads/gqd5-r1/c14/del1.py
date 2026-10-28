import subprocess, sys, random
# edges of dm_q4.edges (flag edges and matching edges); matching edges are those whose endpoints are point/line copies with sigma
base = [tuple(map(int, l.split())) for l in open('dm_q4.edges').read().split('\n')[1:] if l.strip()]
N, m = 85, 6
def is_match(a, b):
    # matching: point copy (a<510) to line copy (b>=510) with flag not in list; determine via file of flags
    return None
flags = set()
import struct
with open('gq/gq_q4.bin', 'rb') as f:
    q, NN, L = struct.unpack('3i', f.read(12))
    lines = [list(struct.unpack(f'5i', f.read(20))) for _ in range(L)]
for l, pts in enumerate(lines):
    for p in pts:
        for h in range(m):
            flags.add((p * m + h, (N + l) * m + h))  # placeholder, real voltages below
# real flag edge set: the flag voltage is hv; count via degrees instead: a matching edge is one whose removal
# matching edges = all edges not in the flag set from the sol file
sol = open('dm_q4.sol').read().split('\n')
vals = list(map(int, ' '.join(sol[2:]).split()))
J = 2
hv = vals[2 * J * N:2 * J * N + N * 5]
fl = set()
for l, pts in enumerate(lines):
    for k, p in enumerate(pts):
        g = hv[l * 5 + k]
        for h in range(m):
            a, b = p * m + h, (N + l) * m + (h + g) % m
            fl.add((min(a, b), max(a, b)))
match = [(min(a, b), max(a, b)) for a, b in base if (min(a, b), max(a, b)) not in fl]
print('matching edges', len(match), file=sys.stderr)
res = []
for i, e in enumerate(match):
    with open('tmp_del.edges', 'w') as f:
        f.write('1020\n')
        for a, b in base:
            if (min(a, b), max(a, b)) != e: f.write(f'{a} {b}\n')
    out = subprocess.run(['./dcount', 'tmp_del.edges', '5'], capture_output=True, text=True).stdout
    bad = int(out.split('pairs_gt_D')[1].split()[0])
    res.append((bad, e))
    if i < 3: print(e, out.strip(), file=sys.stderr)
res.sort()
print('min', res[:5], 'max', res[-3:], 'hist', sorted(set(b for b, _ in res))[:20])
import collections
print(collections.Counter(b for b, _ in res).most_common(10))

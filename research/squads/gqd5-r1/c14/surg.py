"""surg.py: helpers for hub surgery on dm_q4.edges (n=1020, 7-regular, diameter 5).
match: list of the 1020 matching edges (u point copy < 510, v line copy >= 510); flag edges are the rest.
build(deleted_set, hubs): hubs = list of neighbour lists (vertex ids); hub ids n0, n0+1, ...
bad(...): dcount output pairs at distance > 5 (plus maxdeg)."""
import subprocess, os, tempfile
N, m = 85, 6
base = [tuple(map(int, l.split())) for l in open('/home/user/degree-diameter/research/squads/gqd5-r1/c14/dm_q4.edges').read().split('\n')[1:] if l.strip()]
def key(a, b): return (min(a, b), max(a, b))
import struct
_sol = open('/home/user/degree-diameter/research/squads/gqd5-r1/c14/dm_q4.sol').read().split('\n')
_vals = list(map(int, ' '.join(_sol[2:]).split()))
_J = 2
_flags = set()
with open('/home/user/degree-diameter/research/squads/gqd5-r1/c14/gq/gq_q4.bin', 'rb') as f:
    _q, _NN, _L = struct.unpack('3i', f.read(12))
    _lines = [list(struct.unpack('5i', f.read(20))) for _ in range(_L)]
_hv = _vals[2 * _J * N:2 * _J * N + N * 5]
for l, pts in enumerate(_lines):
    for k, p in enumerate(pts):
        g = _hv[l * 5 + k]
        for h in range(m):
            _flags.add(key(p * m + h, (N + l) * m + (h + g) % m))
match = sorted({key(a, b) for a, b in base if key(a, b) not in _flags})
n0 = 1020
def build(deleted, hubs, path):
    """deleted: set of indices into match; hubs: list of neighbour lists"""
    dset = {match[i] for i in deleted}
    edges = [e for e in base if key(*e) not in dset]
    n = n0 + len(hubs)
    for j, nb in enumerate(hubs):
        for v in nb: edges.append((n0 + j, v))
    with open(path, 'w') as f:
        f.write(f'{n}\n' + ''.join(f'{a} {b}\n' for a, b in edges))
    return n
def bad(deleted, hubs, tag='t'):
    path = f'/tmp/c14_{tag}_{os.getpid()}.edges'
    build(deleted, hubs, path)
    out = subprocess.run(['/home/user/degree-diameter/research/squads/gqd5-r1/c14/dcount', path, '5'], capture_output=True, text=True).stdout
    os.remove(path)
    f = out.split()
    return int(f[f.index('pairs_gt_D') + 1]), int(f[f.index('maxdeg') + 1]), out

# mkdesign.py: simple designs for hexlift (text format, see hexlift.c header)
import sys, random, struct
def load(fn):
    b = open(fn, 'rb').read()
    q, N, L = struct.unpack('<3i', b[:12])
    lp = struct.unpack('<%di' % (N * (q + 1)), b[12:12 + 4 * N * (q + 1)])
    return q, N, [lp[i * (q + 1):(i + 1) * (q + 1)] for i in range(N)]
def main():
    kind, fn, m, t, seed, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    random.seed(seed)
    q, N, lines = load(fn)
    M = []
    for k in range(t):
        perm = list(range(N)); random.shuffle(perm); M.append(perm)
    with open(out, 'w') as f:
        f.write('%d %d %d\n' % (q, m, t))
        for p in range(N):
            row = []
            for k in range(t):
                v = (k + 1) % m if kind.startswith('xm') else random.randrange(m)
                row += [M[k][p], v]
            row += [random.randrange(m) if 'sig' in kind else 0 for _ in range(q + 1)]
            f.write(' '.join(map(str, row)) + '\n')
main()

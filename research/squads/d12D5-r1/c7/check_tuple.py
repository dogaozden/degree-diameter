"""Independent check of the k=1 fake cost for one voltage tuple (uses the walk definition from mlift_ejoint.c)."""
import sys
def load(fn):
    v = open(fn).read().split(); n = int(v[0]); T = [[int(v[1 + i * n + j]) for j in range(n)] for i in range(n)]
    e = next(i for i in range(n) if all(T[i][j] == j for j in range(n)))
    inv = [next(j for j in range(n) if T[i][j] == e) for i in range(n)]
    return n, T, e, inv
n, T, e, inv = load(sys.argv[1]); volt = [int(x) for x in sys.argv[2].split(',')]
EA = [0, 0, 0, 0]; EB = [0, 0, 0, 0]
hit = set()
for e1 in range(4):
    for e2 in range(4):
        if e2 != e1:
            x = T[inv[volt[e2]]][volt[e1]]          # v2^-1 v1 (2-walk e1 e2)
            if x != e: hit.add(x)
            for e3 in range(4):
                if e3 == e2: continue
                for e4 in range(4):
                    if e4 == e3: continue
                    x = T[inv[volt[e4]]][T[volt[e3]][T[inv[volt[e2]]][volt[e1]]]]
                    hit.add(x)
print('n', n, 'fake uncovered', n - len(hit), 'tuple', volt)

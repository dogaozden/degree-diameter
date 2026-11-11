# usage: mkgroup.py KIND ARGS OUT ; KIND in cyc m | dih m | meta a r b  (Z_a x|_r Z_b, r^b = 1 mod a)
import sys
kind = sys.argv[1]; out = sys.argv[-1]
els = []; mul = None
if kind == 'cyc':
    m = int(sys.argv[2]); N = m
    T = [[(i+j)%m for j in range(m)] for i in range(m)]
elif kind == 'dih':
    m = int(sys.argv[2]); N = 2*m
    idx = lambda r,s: s*m + r
    T = [[0]*N for _ in range(N)]
    for s1 in range(2):
        for r1 in range(m):
            for s2 in range(2):
                for r2 in range(m):
                    r = (r1 + (r2 if s1==0 else -r2)) % m
                    T[idx(r1,s1)][idx(r2,s2)] = idx(r, (s1+s2)%2)
elif kind == 'meta':
    a, r, bb = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); N = a*bb
    assert pow(r, bb, a) == 1 % a
    idx = lambda i,j: i*bb + j
    T = [[0]*N for _ in range(N)]
    for i1 in range(a):
        for j1 in range(bb):
            for i2 in range(a):
                for j2 in range(bb):
                    i = (i1 + pow(r, j1, a)*i2) % a
                    T[idx(i1,j1)][idx(i2,j2)] = idx(i, (j1+j2)%bb)
# sanity: associativity on random triples and identity 0 (cyc) / check
import random
for _ in range(2000):
    x,y,z = random.randrange(N), random.randrange(N), random.randrange(N)
    assert T[T[x][y]][z] == T[x][T[y][z]]
with open(out,'w') as f:
    f.write('%d\n' % N)
    for row in T: f.write(' '.join(map(str,row))+'\n')
print('group order', N, 'written', out)

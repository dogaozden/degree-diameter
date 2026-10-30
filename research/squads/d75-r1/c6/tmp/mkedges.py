import sys
aff, solfile, out = sys.argv[1], sys.argv[2], sys.argv[3]
line = [l for l in open(solfile) if l.startswith('SOL')][0].split()
S = list(map(int, line[line.index('S') + 1:]))
L = open(aff).read().split('\n'); n = int(L[0].split()[0])
mul = [list(map(int, L[1 + i].split())) for i in range(n)]
with open(out, 'w') as f:
    f.write(f'{2*n}\n')
    for g in range(n):
        for s in S:
            f.write(f'{g} {n + mul[s][g]}\n')
print('S', S)

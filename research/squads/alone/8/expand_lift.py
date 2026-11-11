# Expand a Z_M voltage base ("K M D" then "i j a" lines) into a plain edge list for apsp.c.
# X vertex (i,g) -> i*M+g ; Y vertex (j,g) -> K*M + j*M + g ; edge (i,g)~(j,(g+a)%M).
import sys
lines = open(sys.argv[1]).read().split('\n')
K, M, D = map(int, lines[0].split())
E = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
n = 2 * K * M
with open(sys.argv[2], 'w') as f:
    f.write(f'{n}\n')
    for i, j, a in E:
        for g in range(M):
            f.write(f'{i*M+g} {K*M + j*M + (g+a) % M}\n')
print('lift n', n, 'edges', len(E) * M, file=sys.stderr)

# Expand a Z_m lift design (base file: "156 156 m" then "a b v" lines) into an explicit edge list for apsp_mt.
# Vertex (a,g) -> a*m+g (side A); (b,g) -> 156*m + b*m + g (side B). Edge (a,b,v): (a,g) ~ (b,g+v mod m).
import sys
src, dst = sys.argv[1], sys.argv[2]
L = open(src).read().split('\n')
nA, nB, m = map(int, L[0].split())
E = [tuple(map(int, l.split())) for l in L[1:] if l.strip()]
n = (nA + nB) * m
with open(dst, 'w') as f:
    f.write('%d\n' % n)
    for a, b, v in E:
        for g in range(m):
            f.write('%d %d\n' % (a * m + g, nA * m + b * m + (g + v) % m))
print('wrote', dst, 'n', n, 'edges', len(E) * m)

import sys
m, k, out_grp = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
n = 2 * k * m
def vid(u, h): return u * m + (h % m)
g = [vid(u // m, u % m + 1) for u in range(n)]
G = [tuple(range(n))]
p = list(range(n))
for _ in range(m - 1):
    p = [g[x] for x in p]; G.append(tuple(p))
with open(out_grp, 'w') as f:
    f.write('%d %d\n' % (n, len(G)))
    for q in G: f.write(' '.join(map(str, q)) + '\n')
    f.write(' '.join('0' if v // m < k else '1' for v in range(n)) + '\n')
print('Z%d group written, order %d' % (m, len(G)))

"""Try to add 2 vertices to the 3-copy H(q) graph: delete q+1 edges (a_j, b_j) (a_j white = point side, b_j black),
add x ~ a_1..a_{q+1}, w ~ b_1..b_{q+1}, x ~ w. Degrees stay <= q+2. Score = ordered pairs at distance > 7
(violations.c); 0 would be a graph on 6P + 2 vertices, one more pair than the table.

usage: python3 gadget.py q BASE.edges VIOLATIONS_BIN iters seed [kinds]
kinds: comma list of edge kinds to draw from: m0 (voltage-0 copies of matching edges), cross, hex (other hexagon edges)
Local search: replace one deleted edge at a time, keep if the score does not increase.
"""
import sys, random, subprocess, os, tempfile

q, base, vbin, iters, seed = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
kinds = (sys.argv[6] if len(sys.argv) > 6 else 'm0,cross').split(',')
lines = open(base).read().split('\n')
n = int(lines[0])
E = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
P = n // 6
blk = 2 * P
# classify: cross = endpoints in different copies; m0 = same copy and parallel to a cross edge pattern
cross = [e for e in E if e[0] // blk != e[1] // blk]
Mp = {}
for a, b in cross:          # a = (p, c), b = (M(p), c+1): line index within copy = b % blk - P
    Mp[(a // blk, a % blk)] = b % blk - P
m0, hexo = [], []
for a, b in E:
    if a // blk == b // blk:
        c, p, l = a // blk, a % blk, b % blk - P
        (m0 if Mp.get((c, p)) == l else hexo).append((a, b))
pools = {'m0': m0, 'cross': cross, 'hex': hexo}
pool = [e for k in kinds for e in pools[k]]
rng = random.Random(seed)
tmp = tempfile.NamedTemporaryFile('w', suffix='.edges', delete=False).name


def score(sel):
    S = set(sel)
    with open(tmp, 'w') as f:
        f.write('%d\n' % (n + 2))
        x, w = n, n + 1
        for e in E:
            if e not in S:
                f.write('%d %d\n' % e)
        for a, b in sel:
            f.write('%d %d\n%d %d\n' % (a, x, b, w))
        f.write('%d %d\n' % (x, w))
    out = subprocess.run([vbin, tmp, '7'], capture_output=True, text=True).stdout
    return int(out.split('pairs_beyond_D=')[1].split()[0])


def valid_sel(sel):
    A = [a for a, b in sel]
    B = [b for a, b in sel]
    return len(set(A)) == len(A) and len(set(B)) == len(B)


k = q + 1
while True:
    sel = rng.sample(pool, k)
    if valid_sel(sel):
        break
cur = score(sel)
print('start', cur, flush=True)
best = cur
for it in range(iters):
    j = rng.randrange(k)
    new = list(sel)
    new[j] = rng.choice(pool)
    if not valid_sel(new):
        continue
    s = score(new)
    if s <= cur:
        sel, cur = new, s
        if s < best:
            best = s
            print('it %d score %d sel %s' % (it, s, sel), flush=True)
            if s == 0:
                break
print('final', best, sel)
os.unlink(tmp)

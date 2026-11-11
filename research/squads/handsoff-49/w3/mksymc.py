# Involution sigma (from mksym2.py: seed 6, order 2, allowing fixed vertices, no fixed edges) with multiplier a (a^2 = 1 mod 63):
# writes per edge "orbit coefficient" with volt(sigma e) = a * volt(e). Output: symc_a<a>.txt (read by w3s via SYMC=).
import sys
src = open('mksym2.py').read().split("with open(out, 'w') as f:")[0]
src = src.replace("out = sys.argv[3] if len(sys.argv) > 3 else 'sym.txt'", "out = '/dev/null'")
ns = {}
sys.argv = ['x', '6', '2', '/dev/null', 'allow']
exec(compile(src, 'mksym2', 'exec'), ns)
sig = ns['sig']; edges = ns['edges']
E = {tuple(e): i for i, e in enumerate(edges)}
for a in (62, 8, 55):
    assert (a * a) % 63 == 1
    orb = [-1]*len(edges); coef = [0]*len(edges); K = 0
    for i, (u, v) in enumerate(edges):
        if orb[i] < 0:
            j = E[(sig[u], sig[v])] if (sig[u], sig[v]) in E else E[(sig[v], sig[u])]
            assert j != i, 'fixed edge'
            orb[i] = K; coef[i] = 1; orb[j] = K; coef[j] = a; K += 1
    with open('symc_a%d.txt' % a, 'w') as f:
        f.write("%d %d\n" % (len(edges), K))
        f.write(" ".join("%d %d" % (orb[i], coef[i]) for i in range(len(edges))) + "\n")
    print('a', a, 'orbits', K)

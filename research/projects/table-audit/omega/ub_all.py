import itertools, sys
from ubound import model, bound
for q in map(int, sys.argv[1:]):
    al = (q + 3) // 2
    best = None
    for types in itertools.product('ab', repeat=al):
        if types[0] != 'a': continue
        for inner in itertools.product('LP', repeat=al):
            types_s, inner_s = ''.join(types), ''.join(inner)
            C, lab, cls = model(types_s, inner_s)
            worst = None
            for hl in [(0, 0), (1, 0)]:
                for cp in range(C):
                    if hl in lab[cp]: continue
                    for V in 'PL':
                        b, n, bud = bound(q, types_s, inner_s, hl, cp, V)
                        if worst is None or b < worst[0]: worst = (b, hl, cp, V, bud)
            if best is None or worst[0] > best[0]: best = (worst[0], types_s, inner_s, worst)
    print(q, 'alpha', al, 'n', n, 'best pattern (max over patterns of min over targets of union bound):', best, 'ratio %.2f' % (best[0] / n))

"""w17: print conjugacy class (from runs/A7_list.tsv, order-4 subgroups) for each block of a 4444 cfg file"""
import sys
cls = {}
for line in open('/home/user/degree-diameter/research/squads/handsoff-49/w17/runs/A7_list.tsv'):
    if line.startswith('#'): continue
    p = line.rstrip('\n').split('\t')
    el = tuple(sorted(int(x) for x in p[4].split('=')[1].split())) if False else tuple(sorted(int(x) for x in p[4][len('elems='):].split()))
    cls[el] = (p[2], p[1])
for f in sys.argv[1:]:
    rows = open(f).read().split('\n')[1:]
    out = []
    for r in rows:
        if not r.strip(): continue
        el = tuple(sorted(int(x) for x in r.split()[1:]))
        out.append(cls.get(el, ('?', '?'))[0] + ':' + cls.get(el, ('?','?'))[1])
    print(f.split('/')[-1], out)

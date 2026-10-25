import glob, os, re
rows = []
for f in sorted(glob.glob('/home/user/degree-diameter/research/squads/r2-smallfam/c3/lscreen_b44_*_D10.tsv')):
    base = re.sub(r'^lscreen_|_D10\.tsv$', '', os.path.basename(f))
    scr = skip = 0; best = None
    for l in open(f):
        p = l.rstrip('\n').split('\t')
        if len(p) < 5:
            continue
        if p[2] == '-' or p[1] == '*':
            skip += 1; continue
        scr += 1
        costs = [int(c) for c in p[4].split(',')]
        c = min(costs)
        vol = p[5] if len(p) > 5 else ''
        if best is None or c < best[0]:
            best = (c, p[0], p[1], p[2], vol)
    print(f'{base}: screened={scr} filtered_out={skip} best={best}')

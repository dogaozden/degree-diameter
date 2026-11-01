# Collect chain-end sets (CHAIN lines with S) from ORBW=3 logs of the grind runs: psl and prod groups.
import glob, re, os
R = '/home/user/degree-diameter/research/squads/handsoff-108'
srcs = sorted(glob.glob(R + '/c1-grind/analysis/raw/*.log'))
srcs = [f for f in srcs if 'ORBW=3' in open(f, errors='replace').read(200000)]
srcs += [R + '/c1-grind/g1.log', R + '/c1-grind/g2.log']
out = {'psl': [], 'prod': []}
seen = set()
for f in srcs:
    name = os.path.basename(f)
    grp = 'prod' if 'prod_psl_7' in name or name.startswith('g2') else ('psl' if ('psl_23' in name or name.startswith('g1')) else None)
    if grp is None:
        continue
    k = 0
    for line in open(f, errors='replace'):
        if not line.startswith('CHAIN'):
            continue
        m = re.match(r'CHAIN (\d+) min (\d+) .* S ((?:-?\d+ ){9}-?\d+)\s*$', line)
        if not m:
            continue
        k += 1
        s = m.group(3)
        key = (grp, s)
        if key in seen:
            continue
        seen.add(key)
        out[grp].append('CE%s_%s_%d\t%s' % (grp, m.group(2), len(out[grp]) + 1, s))
for grp in out:
    with open(R.replace('x','') + '/c1b-structure/chainends_%s.txt' % grp, 'w') as fh:
        fh.write('\n'.join(out[grp]) + '\n')
    print(grp, len(out[grp]), 'chain-end sets from', len(srcs), 'logs')

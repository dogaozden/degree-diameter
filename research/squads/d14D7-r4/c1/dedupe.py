# c1 (r4): drop subgroup perm files whose orbit partition duplicates an earlier one (same subgroup seen twice).
import json, hashlib, sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c1')
from survey import cycles
OUT = '/home/user/degree-diameter/research/squads/d14D7-r4/c1/'
S = json.load(open(OUT + 'groups_summary.json'))
seen = {}
keep = []
for e in S:
    p = np.loadtxt(e['perm'], dtype=np.int64)
    part = sorted(tuple(sorted(c)) for c in cycles(p) if len(c) > 0)
    h = hashlib.sha1(repr(part).encode()).hexdigest()[:12]
    if h in seen:
        print('dup', e['tag'], '==', seen[h]); continue
    seen[h] = e['tag']; keep.append(dict(e, phash=h))
json.dump(keep, open(OUT + 'groups_unique.json', 'w'), indent=1)
print(len(S), 'subgroups,', len(keep), 'distinct orbit partitions')
for e in keep:
    if e['usable_orbits'] > 0 and e['order'] >= 4:
        print(e['tag'], e['order'], e['usable_orbits'], e['usable_points'])

import json, sys
rows=[json.loads(l) for l in open('/home/user/degree-diameter/research/squads/thmfam-r1/c6/results.jsonl')]
from collections import defaultdict
best=defaultdict(lambda:None)
for r in rows:
    if 'diam' not in r: print('ERR',r); continue
    k=(r['q'],r['m'])
    if best[k] is None or (r['full'] and r['diam']<best[k]['diam']): best[k]=r
for k,v in sorted(best.items()): print(k, v['target'], 'diam',v['diam'], 'full',v['full'], 't2',v['t2'],'rsel',v['rsel'])

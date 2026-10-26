import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r4/h01')
import scan
import numpy as np
names = sys.argv[1:]
out = open('/home/user/degree-diameter/research/squads/b48/r4/h01/results.txt', 'a')
for nm in names:
    r = scan.run(f'/home/user/degree-diameter/research/squads/b48/r4/h01/groups/{nm}.bin', limit=2)
    line = f"{nm} N={r['N']} reps={r['reps']} lines={r['lines']} {r['err']} secs={r['secs']}"
    print(line, flush=True); out.write(line + '\n')
    for h in r['hits']:
        out.write('  HIT ' + nm + ' ' + h + '\n')
    out.flush()

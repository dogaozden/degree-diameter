#!/usr/bin/env python3
"""Run orbclq (one heavy process at a time) on every J1 subgroup in subgroups/manifest.json."""
import json, os, re, subprocess, sys, time
HERE = '/home/user/degree-diameter/research/squads/d14D7-r5/c2'
ORB = '/home/user/degree-diameter/research/cell147/ovoid/orbclq'
T = sys.argv[1] if len(sys.argv) > 1 else '15'
man = json.load(open(os.path.join(HERE, 'subgroups', 'manifest.json')))
log = open(os.path.join(HERE, 'runs.log'), 'a')
res = []
for m in man:
    base = os.path.basename(m['file'])[:-4]
    out = os.path.join(HERE, 'sets', base + '.txt')
    t = time.time()
    try:
        p = subprocess.run(['timeout', '300', 'nice', '-n', '10', ORB, m['file'], '-t', T, '-s', '1', '-o', out],
                           capture_output=True, text=True)
        line = [l for l in p.stdout.splitlines() if l.startswith('RESULT')]
        line = line[-1] if line else 'NORESULT ' + p.stderr[-200:].replace('\n', ' | ')
    except Exception as e:
        line = 'ERR ' + str(e)
    best = re.search(r'best=(\d+)', line)
    good = re.search(r'good=(\d+)', line)
    rec = dict(file=out, size=m['size'], name=base, best=int(best.group(1)) if best else -1,
               good=int(good.group(1)) if good else -1, line=line, sec=round(time.time() - t, 1))
    res.append(rec)
    log.write(json.dumps(rec) + '\n'); log.flush()
    print(base, rec['best'], rec['good'], rec['sec'], flush=True)

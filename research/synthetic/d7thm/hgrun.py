#!/usr/bin/env python3
"""Computer checks of HG(K_B, K_A; q-k) for the (q, k) not covered by Lemmas 4.1-4.2 (hubsum.out), q = 11..27, k <= 6,
with m = q^2+1 (Theorem 3.4 slot counts).  Random bipartite graphs (hgcheck rand) for K <= 300,000, else Haar graphs
of Z_K with K = K_A on both sides (hgcheck haar; equal sides, so the B side gets K_A <= K_B hubs).  Output: hgrun.out"""
import subprocess, re
from hubcap_lib import slots
HG = '/tmp/claude-0/hgcheck'
unc = {}
for line in open('hubsum.out'):
    m = re.match(r'k=(\d+): NOT covered: \[(.*)\]', line)
    if m:
        unc[int(m.group(1))] = [int(x) for x in m.group(2).split(',') if x.strip()]
done = {}
try:
    for line in open('hgrun.out'):
        mm = re.match(r'q=(\d+) k=(\d+) ', line)
        if mm and 'RESULT VALID' in line:
            done[(int(mm.group(1)), int(mm.group(2)))] = line
except FileNotFoundError:
    pass
out = open('hgrun.out', 'w')
for line in done.values():
    out.write(line)
for k in range(2, 7):
    for q in unc.get(k, []):
        if q < 11 or q > 27:
            continue
        if (q, k) in done:
            continue
        KB, KA = slots(q, k); d = q - k
        res = None
        if max(KB, KA) <= 300000:
            for seed in range(1, 5):
                r = subprocess.run([HG, 'rand', str(KB), str(KA), str(d), str(seed)], capture_output=True, text=True, timeout=3600).stdout
                res = ('rand seed %d' % seed, r.strip().splitlines())
                if 'RESULT VALID' in r:
                    break
            if 'RESULT VALID' not in r:
                far = int(re.search(r'far_same_colour_pairs=(\d+)', r).group(1)) if 'far_same' in r else 10 ** 9
                if far <= 20000 and max(KB, KA) <= 60000:
                    r = subprocess.run([HG, 'rand', str(KB), str(KA), str(d), '1', 'repair'], capture_output=True, text=True, timeout=7200).stdout
                    res = ('rand seed 1 + aimed 2-switch repair', r.strip().splitlines())
        if res is None or 'RESULT VALID' not in res[1][-1]:
            r = subprocess.run([HG, 'haar', str(KA), str(d), '1', '30'], capture_output=True, text=True, timeout=3600).stdout
            res2 = ('haar K_A on both sides', r.strip().splitlines()[-2:])
            res = ((res[0] + ' | ' if res else '') + res2[0], (res[1] if res else []) + res2[1])
        s = 'q=%d k=%d d=%d K_B=%d K_A=%d: %s: %s' % (q, k, d, KB, KA, res[0], ' / '.join(res[1]))
        print(s, flush=True); out.write(s + '\n'); out.flush()

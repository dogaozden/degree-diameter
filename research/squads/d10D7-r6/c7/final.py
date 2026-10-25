"""Pick the best VALID candidate (official setcheck), copy it to best_final.txt, and print the scoreboard line."""
import glob, json, subprocess, os
D = '/home/user/degree-diameter/research/squads/d10D7-r6/c7/'
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q11.bin'
CHK = '/home/user/degree-diameter/research/squads/d10D7-r4/tools/setcheck'
cands = sorted(set(glob.glob(D + 'best_*.txt') + glob.glob(D + 'union_*.txt') + glob.glob(D + 'tabu*_s*.txt')))
res = []
for f in cands:
    if f.endswith('.log'): continue
    out = subprocess.run([CHK, HEX, f, 'points', 'opposite'], capture_output=True, text=True, timeout=600).stdout.strip()
    ok = out.startswith('VALID')
    size = int(out.split()[2]) if ok else 0
    res.append((size, os.path.basename(f), out))
    print(os.path.basename(f), '->', out, flush=True)
best = max(res)
print('BEST', best)

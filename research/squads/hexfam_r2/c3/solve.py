"""usage: solve.py NAME SECONDS SEED [useseed]  -> runs wils on graphs/NAME.bin, writes sets/NAME_s<SEED>.txt, scores it."""
import sys, subprocess, numpy as np, os
D = '/home/user/degree-diameter/research/squads/hexfam_r2/c3'
name, secs, seed = sys.argv[1], sys.argv[2], sys.argv[3]
useseed = len(sys.argv) > 4 and sys.argv[4] == 'seed'
z = np.load('%s/graphs/%s.npz' % (D, name))
S, sizes, order, starts, seedv = z['S'], z['sizes'], z['order'], z['starts'], z['seed']
out = '%s/sets/%s_s%s.ids' % (D, name, seed)
cmd = ['timeout', '1000', 'nice', '-n', '10', '%s/wils' % D, '%s/graphs/%s.bin' % (D, name), out, secs, seed]
if useseed:
    sf = '%s/sets/%s_seed.ids' % (D, name); np.savetxt(sf, seedv, fmt='%d'); cmd.append(sf)
r = subprocess.run(cmd, capture_output=True, text=True)
print(r.stdout.strip(), r.stderr.strip().splitlines()[-1] if r.stderr.strip() else '', flush=True)
ch = np.loadtxt(out, dtype=np.int64, ndmin=1)
pts = np.concatenate([order[starts[i]:starts[i] + sizes[i]] for i in ch]) if len(ch) else np.array([], dtype=np.int64)
pts = np.sort(pts)
setf = '%s/sets/%s_s%s_%d.txt' % (D, name, seed, len(pts))
np.savetxt(setf, pts, fmt='%d')
res = subprocess.run(['/home/user/degree-diameter/research/projects/hexagon-family/tools/povcheck',
                      '/home/user/degree-diameter/research/projects/hexagon-family/hex/hex_q11.bin', setf], capture_output=True, text=True)
print(name, 'seed', seed, 'orbits', len(ch), 'points', len(pts), '|', res.stdout.strip().splitlines()[-1], flush=True)

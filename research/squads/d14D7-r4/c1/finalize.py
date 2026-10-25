# c1 (r4): pick the best orbitclique result (largest P among logs with 0 orthogonal pairs), re-score its flags file
# with the pack CHECKONLY scorer, and print the summary. Does not write the scoreboard.
import glob, re, subprocess, os
C = '/home/user/degree-diameter/research/squads/d14D7-r4/c1/'
best = None
for lg in sorted(glob.glob(C + 'log_*.txt')):
    txt = open(lg).read()
    m = re.findall(r'best: (\d+) orbits, (\d+) points, orthogonal pairs (\d+)', txt)
    if not m: continue
    orbs, pts, bad = map(int, m[-1])
    tag = os.path.basename(lg)[4:-4]
    print(f"{tag:45s} orbits={orbs:4d} points={pts:4d} orth_pairs={bad}")
    if bad == 0 and (best is None or pts > best[1]):
        best = (tag, pts)
if best:
    tag, pts = best
    flags = C + f'flags_{tag}.txt'
    env = dict(os.environ, CHECKONLY='1')
    out = subprocess.run(['/home/user/degree-diameter/research/cell147/units/pack',
                          '/home/user/degree-diameter/research/cell147/data/gh_11.txt', '0', '1', '/dev/null', flags],
                         env=env, capture_output=True, text=True).stdout.strip()
    print('BEST', tag, 'points', pts, 'flags', flags)
    print('CHECKONLY', out)

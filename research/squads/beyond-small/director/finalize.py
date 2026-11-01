#!/usr/bin/env python3
"""finalize.py: put the best recorded (17,5) value into BEYOND_SMALL.md, results.py / BEYOND_TABLE.md and the graph
folder of research/frontier/beyond (job beyond-small). Reads research/squads/beyond-small/graphs/d17D5_n*.check.txt."""
import glob, os, re, shutil, subprocess
ROOT = '/home/user/degree-diameter'
G = f'{ROOT}/research/squads/beyond-small/graphs'
B = f'{ROOT}/research/frontier/beyond'
best = max(int(re.search(r'n(\d+)\.check', p).group(1)) for p in glob.glob(f'{G}/d17D5_n*.check.txt'))
chk = open(f'{G}/d17D5_n{best}.check.txt').read()
assert f'RESULT VALID d=17 D=5 n={best}' in chk
H = 16896
bases = [l for l in open(f'{G}/d17D5_n{best}_orbit_bases.txt') if l.strip()]
na = sum(1 for l in bases if int(l.split()[0]) >= H); nb = len(bases) - na
assert 33792 + 22 * (na + nb) == best
pct = 100.0 * best / 139804
print('best', best, 'A', na, 'B', nb, f'{pct:.2f} %')
# BEYOND_SMALL.md
p = f'{B}/BEYOND_SMALL.md'; s = open(p).read()
s = s.replace('BEST_N = 33,792 + 22·(BEST_A + BEST_B) hubs (BEST_A orbits on side A, BEST_B on side B)',
              f'{best:,} = 33,792 + 22·({na} + {nb}) hubs ({na} orbits on side A, {nb} on side B)')
s = s.replace('d17D5_nBEST_N', f'd17D5_n{best}')
s = re.sub(r'\| \(17,5\) \| \*\*[\d,]+\*\* \| [\d.]+ \| 139,804 \| \*\*new\*\*: the \(16,5\) route-chart graph \+ [\d,]+ hubs in \d+ Z22-orbits \(below\) \| apsp \([^)]*\) \|',
           f'| (17,5) | **{best:,}** | {pct:.1f} | 139,804 | **new**: the (16,5) route-chart graph + {22*(na+nb):,} hubs in {na+nb} Z22-orbits (below) | apsp (research/squads/beyond-small/graphs/d17D5_n{best}.check.txt) |', s)
open(p, 'w').write(s)
# results.py + splice
p = f'{B}/results.py'; s = open(p).read()
S = 'research/squads/beyond-small'
new = (f'add(17, 5, {best}, "(16,5) route-chart graph + {22*(na+nb):,} hubs (new vertices joined to 4 affine fibre lines of old '
       f'vertices) in {na+nb} Z22-orbits: {na} on side A, {nb} on side B (job beyond-small, BEYOND_SMALL.md)", '
       f'"apsp: {S}/graphs/d17D5_n{best}.check.txt", "{S}/graphs/d17D5_n{best}_orbit_bases.txt; builder {S}/graphs/build_d17D5_hubs.py")')
s = re.sub(r'^add\(17, 5, .*$', new.replace('\\', '\\\\'), s, count=1, flags=re.M)
open(p, 'w').write(s)
subprocess.run(['python3', f'{B}/splice.py'], check=True)
# copies next to the other beyond-table graphs
shutil.copy(f'{G}/d17D5_n{best}_orbits.edges.gz', f'{B}/graphs/d17D5_n{best}_hubs_z22orbits.edges.gz')
shutil.copy(f'{G}/d17D5_n{best}.check.txt', f'{B}/checks/d17D5_n{best}_hubs_z22orbits.apsp.txt')
print('done')

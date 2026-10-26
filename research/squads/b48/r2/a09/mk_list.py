import subprocess
lines = []
# abc groups from abc.py list 547 700 --nonmeta
out = subprocess.run(['python3', '/home/user/degree-diameter/research/squads/b48/tools/abc.py', 'list', '547', '700', '--nonmeta'], capture_output=True, text=True).stdout
for l in out.split('\n'):
    p = l.split()
    if len(p) < 3: continue
    k, comps, N = p[0], p[1], p[2]
    cs = ','.join(':'.join(c.split(':')[:2]) for c in comps.split(','))
    lines.append(('abc', N, f'{k} {cs}'))
for l in open('meta_dedup.txt'):
    N, m, k, r, o = l.split()
    lines.append(('meta', N, f'meta {m} {k} {r}'))
with open('screen_list.txt', 'w') as f:
    for kind, N, spec in lines:
        f.write(f'{kind}\t{N}\t{spec}\n')
print(len(lines))

# rewrites the "Live chain-minimum histogram" block of NOTES.md from g1.log and g2.log (CHAIN lines)
import re, collections, time
base = '/home/user/degree-diameter/research/squads/handsoff-108/c1-grind/'
lines = ['## Live chain-minimum histogram (this worker, ORBW=3 units; energy is always a multiple of 3)', '',
         f'(refreshed {time.strftime("%H:%M", time.gmtime())} UTC by update_live.py)', '']
for tag in ('g1', 'g2'):
    mins = []
    for l in open(base + tag + '.log', errors='replace'):
        m = re.match(r'CHAIN \d+ min (\d+) secs (\d+)', l)
        if m: mins.append(int(m.group(1)))
    c = collections.Counter(mins)
    lines.append(f'- {tag}: chains {len(mins)}, best {min(mins) if mins else "-"}, median {sorted(mins)[len(mins)//2] if mins else "-"}, '
                 + ' '.join(f'{k}:{c[k]}' for k in sorted(c)))
lines.append('')
txt = open(base + 'NOTES.md').read()
new = re.sub(r'## Live chain-minimum histogram.*?(?=\n## )', '\n'.join(lines) + '\n', txt, count=1, flags=re.S)
open(base + 'NOTES.md', 'w').write(new)
print('\n'.join(lines))

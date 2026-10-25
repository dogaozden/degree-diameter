import sys
Q = '/home/user/degree-diameter/research/squads/d16D7_r3/quot/'
seedf, name, outq = sys.argv[1], sys.argv[2], sys.argv[3]
seed = set(int(l) for l in open(seedf) if l.strip() and not l.startswith('#'))
mp = [list(map(int, l.split())) for l in open(Q + name + '.map')]
inside = [i for i, m in enumerate(mp) if all(v in seed for v in m)]
partial = [i for i, m in enumerate(mp) if any(v in seed for v in m) and not all(v in seed for v in m)]
covered = sum(len(mp[i]) for i in inside)
print(name, 'seed size', len(seed), 'quotient vertices fully inside seed', len(inside), 'weight', covered, 'partially hit', len(partial))
print('seed elements not covered by any quotient vertex', len(seed) - covered)
open(outq, 'w').write('\n'.join(map(str, inside)) + '\n')

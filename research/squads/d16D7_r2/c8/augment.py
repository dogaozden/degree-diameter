import sys
D = '/home/user/degree-diameter/research/squads/d16D7_r2/'
g, solf, out = sys.argv[1], sys.argv[2], sys.argv[3]
with open(g) as f:
    M, E = map(int, f.readline().split())
    nb = [None] * M
    for line in f:
        a = list(map(int, line.split())); nb[a[0]] = set(a[3:3 + a[2]])
S = set(int(x) for x in open(solf).read().split() if x.strip())
blocked = set()
for v in S: blocked |= nb[v]
assert not (blocked & S)
free = [v for v in range(M) if v not in S and not (nb[v] & S)]
print('solution', len(S), 'free vertices', len(free))
import random
random.seed(1)
random.shuffle(free)
for v in free:
    if not (nb[v] & S):
        S.add(v)
print('after greedy augmentation', len(S))
with open(out, 'w') as f:
    f.write('\n'.join(map(str, sorted(S))) + '\n')

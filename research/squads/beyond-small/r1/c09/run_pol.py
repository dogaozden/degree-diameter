import sys, time
sys.argv = ['x']
from gq import *
G = build(8)
t = time.time()
for seed in range(1, 200):
    try:
        phi = find_polarity(G, seed=seed, limit_nodes=3000)
    except RuntimeError:
        print('seed', seed, 'node limit', round(time.time()-t,1), flush=True); continue
    if phi is not None:
        print('found seed', seed, 'valid', check_auto(G, phi), 'time', round(time.time() - t, 1), flush=True)
        open('/home/user/degree-diameter/research/squads/beyond-small/r1/c09/polarity_q8.txt', 'w').write(' '.join(map(str, phi)) + '\n')
        break
    print('seed', seed, 'no polarity', round(time.time()-t,1), flush=True)

import random, sys
from gq import build, check_auto
from polar import compose, order, power
q = 8
G = build(q); N = G['N']; V = 2 * N
gens = [list(map(int, l.split())) for l in open('w8_gens.txt') if l.strip()]
rng = random.Random(11)
pool = [g[:] for g in gens] + [list(range(V)) for _ in range(4)]
for _ in range(60):   # mix the pool
    i, j = rng.sample(range(len(pool)), 2); pool[i] = compose(pool[i], pool[j])
found = None; cnt = 0
for step in range(5000):
    i, j = rng.sample(range(len(pool)), 2)
    pool[i] = compose(pool[i], pool[j]) if rng.random() < 0.5 else compose(pool[j], pool[i])
    el = pool[i]
    if el[0] >= N:
        o = order(el)
        if o % 4 == 2:
            inv = power(el, o // 2); cnt += 1
            if check_auto(G, inv):
                found = inv; print('step', step, 'order', o, 'polarity ok', flush=True); break
            else:
                print('check failed'); 
print('found', found is not None, 'swap candidates', cnt)
if found:
    open('polarity_q8.txt', 'w').write(' '.join(map(str, found)) + '\n')

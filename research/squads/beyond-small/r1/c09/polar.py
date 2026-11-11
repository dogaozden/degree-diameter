# Random elements of Aut(incidence graph of W(q)) from nauty generators; pick an involution swapping points and lines.
import re, random, sys
sys.argv = sys.argv[:1] + sys.argv[1:]
from gq import build, check_auto

def parse_gens(path, V):
    txt = open(path).read()
    txt = txt.split('orbit')[0]  # cycles are printed before the orbit summary line
    gens = []
    for m in re.finditer(r'\(([^()]*)\)', txt):
        cyc = [int(x) for x in re.findall(r'\d+', m.group(1))]
        if len(cyc) > 1:
            gens.append(cyc)
    # rebuild permutations: each generator is printed as a sequence of cycles; split on blank lines is unreliable,
    # so rely on the count of generators from the summary line and group cycles by their support covering V.
    perms = []
    cur = list(range(V)); covered = set()
    for cyc in gens:
        if covered & set(cyc):   # a new generator starts when a point repeats
            perms.append(cur); cur = list(range(V)); covered = set()
        for i, a in enumerate(cyc):
            cur[a] = cyc[(i + 1) % len(cyc)]
        covered |= set(cyc)
    perms.append(cur)
    return perms

def compose(p, q_):   # first q_, then p
    return [p[q_[i]] for i in range(len(q_))]

def order(p):
    V = len(p); seen = [False] * V; from math import lcm; o = 1
    for i in range(V):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; l += 1
            o = lcm(o, l)
    return o

def power(p, k):
    r = list(range(len(p))); b = p[:]
    while k:
        if k & 1: r = compose(b, r)
        b = compose(b, b); k >>= 1
    return r

if __name__ == '__main__':
    q = 8
    G = build(q); N = G['N']; V = 2 * N
    gens = parse_gens('/home/user/degree-diameter/research/squads/beyond-small/r1/c09/w8_out.txt', V)
    print('gens parsed', len(gens), [sum(1 for i in range(V) if g[i] != i) for g in gens], flush=True)
    rng = random.Random(7)
    # product replacement style random walk
    cur = list(range(V))
    pool = [g[:] for g in gens]
    for _ in range(50):
        pool.append(list(range(V)))
    # random elements via products of random pool entries
    found = None; tries = 0
    state = [g[:] for g in gens]
    x = list(range(V))
    for step in range(20000):
        i, j = rng.sample(range(len(pool)), 2)
        pool[i] = compose(pool[i], pool[j]) if rng.random() < 0.5 else compose(pool[j], pool[i])
        el = pool[i]
        if el[0] >= N:          # swaps points and lines
            o = order(el)
            if o % 4 == 2:
                tries += 1
                inv = power(el, o // 2)
                assert inv[inv[0]] == 0
                ok = check_auto(G, inv)
                print('step', step, 'order', o, 'involution swap found, check_auto', ok, flush=True)
                if ok:
                    found = inv; break
    if found is not None:
        open('/home/user/degree-diameter/research/squads/beyond-small/r1/c09/polarity_q8.txt', 'w').write(' '.join(map(str, found)) + '\n')
        print('saved polarity')
    else:
        print('none found', tries)

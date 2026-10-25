import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D8-r2/c6')
import design, rainbow, gq
q, k, seed, rf, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == 'random', sys.argv[5]
V, m, E, f = design.design(q, k, seed, random_f=rf)
gq.write_base(out, V, m, E)
print('wrote', out, 'm', m, 'f', f, 'eval:', rainbow.evaluate(out, 6)[1])

import re, sys
P = 191; NZ = 61; AG = (0, 190, 1, 190)  # conj matrix printed by haar_w07 for SL(2,191) x Z61
def mm(x, y):
    a, b, c, d = x; e, f, g, h = y
    return ((a*e+b*g) % P, (a*f+b*h) % P, (c*e+d*g) % P, (c*f+d*h) % P)
def inv(x):
    a, b, c, d = x; return (d % P, (-b) % P, (-c) % P, a % P)
def parse_mat(s):
    return tuple(int(t) % P for t in re.findall(r'-?\d+', s)[:4])
def first_gen(orbfile):
    lines = open(orbfile).read().splitlines()
    m = re.search(r'mat\(([^)]*)\)\s*z=(-?\d+)', lines[1])
    return parse_mat(m.group(1)), int(m.group(2))
def classify(x, z, s0=None):
    y = x
    if s0 is not None:  # T-model hole x = s0 y s0^-1  => y = s0^-1 x s0
        y = mm(mm(inv(s0), x), s0)
    if y[1] == 0 and y[2] == 0:
        return 'central(-I,z=%d)' % z if y[0] == P-1 else ('central(I,z=%d)' % z if z else 'identity')
    if z == 0 and mm(y, AG) == mm(AG, y):
        return 'torus(alpha-fixed)'
    return 'generic'
def run(evalfile, orbfile=None):
    s0 = None; zs0 = 0
    if orbfile:
        s0, zs0 = first_gen(orbfile)
    cnt = {}; lines = open(evalfile).read().splitlines()
    print(evalfile, [l for l in lines if l.startswith('EVAL')])
    for l in lines:
        m = re.match(r'uncovered \d+ mat\(([^)]*)\) z=(-?\d+)(.*)', l)
        if not m: continue
        x = parse_mat(m.group(1)); z = int(m.group(2)) % NZ; side = 'B' if 'B side' in m.group(3) else 'A'
        cls = classify(x, z, s0 if orbfile else None)
        if cls.startswith('central'): cls = 'central(-I)' if '-I' in cls else 'central(I,z!=0)'
        cnt[(side, cls)] = cnt.get((side, cls), 0) + 1
        if cls != 'generic': print('  ', side, cls, 'mat', x, 'z', z)
    print('  counts', sorted(cnt.items()))
if __name__ == '__main__':
    run(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None)

import itertools, sys
def model(types, inner):
    A = len(types); C = 5*A
    # labels: (bar,k). for each copy: dict label -> 'I' or 'O'
    lab = [dict() for _ in range(C)]
    for B,ty in enumerate(types):
        for k in range(5):
            for bar in (0,1):
                if ty=='a':
                    cs, io = ((k-1,k+1),'I') if bar==0 else ((k+2,k+3),'O')
                else:
                    cs, io = ((k+3,k+4),'O') if bar==0 else ((k-1,k+1),'I')
                for c in cs: lab[5*B+c%5][(bar,k)] = io
    cls = lambda c, io: (inner[c//5] if io=='I' else ('P' if inner[c//5]=='L' else 'L'))
    return C, lab, cls
def spheres(q): return [1, q+1, q*(q+1), q*q*(q+1), q**3*(q+1), q**4*(q+1), q**5]
def color(c, cl, types, inner):
    # W = color of unbarred hubs. unbarred touch inner of a-copies, outer of b-copies -> those are Bk(1)
    io = 'I' if cl==inner[c//5] else 'O'
    ty = types[c//5]
    touched_by_unbarred = (ty=='a' and io=='I') or (ty=='b' and io=='O')
    return 1 if touched_by_unbarred else 0
def bound(q, types, inner, hl, cp, V):
    C, lab, cls = model(types, inner); S = spheres(q); n = sum(S[0::2])
    hubcolor = hl[0]  # unbarred=0 (W), barred=1
    vcol = color(cp, V, types, inner)
    budget = 8 if vcol==hubcolor else 7
    adj = [c for c in range(C) if hl in lab[c]]
    assert cp not in adj
    def ball(fromcls, tocls, r):
        par = 0 if fromcls==tocls else 1
        return sum(S[d] for d in range(par, r+1, 2)) if r>=0 else 0
    tot = 0; centers = set(); detail=[]
    seen1 = set(); seen2 = set()
    for c1 in adj:
        X = cls(c1, lab[c1][hl])
        for l1, io in lab[c1].items():
            if l1==hl: continue
            M = cls(c1, io)
            if l1 in lab[cp] and (c1, M, cls(cp, lab[cp][l1])) not in seen1:
                seen1.add((c1, M, cls(cp, lab[cp][l1])))
                Y = cls(cp, lab[cp][l1])
                par = 0 if X==M else 1
                cov = 0
                for a in range(par, 7, 2):
                    if a==0: centers.add(Y); continue
                    rb = budget-3-a
                    if rb < 0: break
                    cov += S[a]*ball(Y, V, rb)
                tot += cov; detail.append((c1,l1,cov))
            # two hops
            for c2 in range(C):
                if c2==c1 or c2==cp or l1 not in lab[c2]: continue
                Z = cls(c2, lab[c2][l1])
                for l2, io2 in lab[c2].items():
                    if l2==l1 or l2 not in lab[cp]: continue
                    M2 = cls(c2, io2); Y2 = cls(cp, lab[cp][l2])
                    key = (c1, M, c2, Z, M2, Y2)
                    if key in seen2: continue
                    seen2.add(key)
                    pa = 0 if X==M else 1; pb = 0 if Z==M2 else 1
                    for a in range(pa, 3, 2):
                        for b in range(pb, 3, 2):
                            rc = budget-5-a-b
                            if rc < 0: continue
                            if a==0 and b==0: continue  # same-row: lands on M_cp(t) centers
                            tot += S[a]*S[b]*ball(Y2, V, rc)
    for Y in centers: tot += ball(Y, V, budget-3)
    return tot, n, budget
if __name__ == '__main__':
    q = int(sys.argv[1]); types = sys.argv[2]; inner = sys.argv[3]
    C,lab,cls = model(types, inner)
    worst = None
    for hl in [(0,0),(1,0)]:
        for cp in range(C):
            if hl in lab[cp]: continue
            for V in 'PL':
                b, n, bud = bound(q, types, inner, hl, cp, V)
                if worst is None or b < worst[0]: worst = (b, hl, cp, V, bud)
                if len(sys.argv) > 4: print(hl, cp, V, bud, b, n)
    print(q, types, inner, 'worst union bound', worst, 'n =', n)

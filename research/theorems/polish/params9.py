# q = 9 (F_9 = F_3[i], i^2 = -1): first c with -c a non-square and (c0,c1) with G zero-free on F^2 \ {0}.
els=[(a,b) for a in range(3) for b in range(3)]
add=lambda x,y:((x[0]+y[0])%3,(x[1]+y[1])%3)
mul=lambda x,y:((x[0]*y[0]-x[1]*y[1])%3,(x[0]*y[1]+x[1]*y[0])%3)
neg=lambda x:((-x[0])%3,(-x[1])%3)
Z=(0,0); sq={mul(x,x) for x in els}
nm=lambda x: f'{x[0]}+{x[1]}i'
def good(c,c0,c1):
    for a in els:
        for b in els:
            if (a,b)==(Z,Z): continue
            if add(mul(add(mul(c0,a),mul(c1,b)),add(mul(a,a),mul(c,mul(b,b)))),neg(mul(b,mul(b,b))))==Z: return False
    return True
for c in els:
    if c==Z or neg(c) in sq: continue
    sol=next(((c0,c1) for c0 in els if c0!=Z for c1 in els if good(c,c0,c1)),None)
    print('q=9 c',nm(c),'(c0,c1)',nm(sol[0]),nm(sol[1])); break

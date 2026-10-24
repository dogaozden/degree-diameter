import itertools
def q_order(kind, q):
    if kind=='sl': return q*(q*q-1)
    if kind=='pgl': return q*(q*q-1)
    if kind=='psl':
        if q%2==0: return q*(q*q-1)
        return q*(q*q-1)//2
    if kind=='agl1': return q*(q-1)
# basic factor list (kind,q) with order
basic=[]
for q in [2,3,4,5,7,8,9,11,13]:
    basic.append(('sl',q,q_order('sl',q)))
for q in [3,5,7,9,11,13]:
    basic.append(('psl',q,q_order('psl',q)))
for q in [2,3,4,5,7,9,11,13]:
    basic.append(('pgl',q,q_order('pgl',q)))
for q in [3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47]:
    basic.append(('agl1',q,q_order('agl1',q)))
# drop duplicates that equal sl (psl 4, psl 8 are sl) -- psl q even not generated
ords=[b[2] for b in basic]
res=[]
def addn(name_parts, order):
    for n in range(1, 2101):
        N = order*n
        if 2001 <= N <= 2100:
            res.append((N, n, ' '.join(name_parts)))
for b in basic:
    addn([b[0],str(b[1])], b[2])
for a,b in itertools.combinations_with_replacement(basic,2):
    o=a[2]*b[2]
    if o<=2100:
        addn([a[0],str(a[1]),b[0],str(b[1])], o)
for a,b,c in itertools.combinations_with_replacement(basic,3):
    o=a[2]*b[2]*c[2]
    if o<=2100:
        addn([a[0],str(a[1]),b[0],str(b[1]),c[0],str(c[1])], o)
# Note: for nested products prod A prod B C -> same orders.
res.sort()
for N,n,s in res:
    print(N, n, s)

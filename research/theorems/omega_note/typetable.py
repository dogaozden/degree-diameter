from math import comb
q=7; X=q**3-q; K=(q+1)**2
types=[((5,),()),((1,4),()),((2,3),()),((1,1,3),()),((1,1,3),(3,)),((1,2,2),()),((1,2,2),(3,)),((1,2,2),(3,3)),
       ((1,1,1,2),()),((1,1,1,2),(3,)),((1,1,1,2),(3,3)),((1,1,1,2),(4,)),
       ((1,1,1,1,1),()),((1,1,1,1,1),(3,)),((1,1,1,1,1),(3,3)),((1,1,1,1,1),(4,)),((1,1,1,1,1),(5,))]
for cls,rich in types:
    A=sum(comb(s,2) for s in cls)
    # triples with three distinct classes
    from itertools import combinations
    lab=[i for i,s in enumerate(cls) for _ in range(s)]
    T=sum(1 for c in combinations(range(5),3) if len({lab[i] for i in c})==3)
    R3=sum(comb(m,3) for m in rich)
    if 5 in rich: U=5*q**4-4*X
    else: U=5*q**4-(10-A)*X+(T-R3)*K+R3*X
    F=q**5-U-140*q*q
    p=sum(s+comb(s,2) for s in cls if s>=2)+sum(comb(m,2) for m in rich)
    print(f"{str(cls):16} {str(rich):8} A={A:2} T={T:2} R3={R3} U={U:6} F={F:6} p={p:2}")

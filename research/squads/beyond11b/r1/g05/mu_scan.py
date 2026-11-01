import math
def W(d,D):
    h=(D-1)//2
    return 1+d*sum((d-1)**(2*i-1) for i in range(1,h+1))
rec11={3:1474,4:24360,5:297648,6:2094960,7:11012976,8:45329808,9:155250816,10:460691568,11:1241299248}
rec12={3:2176,4:68544,5:1041768,6:9366240,7:59838504,8:284095056,9:1105785120}
groups={'SL(2,27)':19656,'SL(2,125)':1953000,'SL(2,243)':14348664,'SL(2,343)':40353264,'SL(2,49)':117600,'SL(2,81)':265680,'SL(2,169)':4818240}
for D,rec in ((11,rec11),(12,rec12)):
  print("D",D)
  for g,N0 in sorted(groups.items(), key=lambda t:t[1]):
    for n in range(1,40):
        N=N0*n
        for d in range(3,12):
            if d not in rec: continue
            w=W(d,D) if D==11 else None
            if w is None: continue
            mu=N*math.exp(-w/N)
            verts=2*N
            if 3<=mu<=20 and verts>rec[d]:
                print(f"{g} n={n} N={N} d={d} mu={mu:.2f} verts={verts} rec={rec[d]} ratio={verts/rec[d]:.3f}")

import sys
L=open(sys.argv[1]).read().split(); n=int(L[0]); E=set()
for i in range(1,len(L),2):
    a,b=int(L[i]),int(L[i+1]); E.add((min(a,b),max(a,b)))
ORD=int(sys.argv[2]); half=n//2
def sigma(v):
    # orbit blocks of size ORD inside A (0..half-1) and B (half..n-1)
    if v<half: base=(v//ORD)*ORD; return base+((v-base+1)%ORD)
    w=v-half; base=(w//ORD)*ORD; return half+base+((w-base+1)%ORD)
ok=all(tuple(sorted((sigma(a),sigma(b)))) in E for a,b in E)
print("sigma (shift within blocks of",ORD,") is automorphism:",ok)

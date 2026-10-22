"""Ranking heuristic for Haar (bi-Cayley) graphs at diameter D.
Haar graph on G x {A,B}, |S| = Delta: vertices (g,A),(g,B); (g,A)~(sg,B).
Binding word count W (distinct reduced words reachable from (e,A) on the binding side):
  D odd = 2k+1: same side, even lengths <= 2k: W = 1 + sum_{i=1..k} Delta (Delta-1)^(2i-1)
  D even = 2k : other side, odd lengths <= 2k-1: W = Delta * sum_{i=0..k-1} (Delta-1)^(2i)
Heuristic max side order N_h: words behave like independent uniform elements, the S-space has N^Delta points,
so a cover exists roughly when N exp(-W/N) < Delta ln N. Calibrated on our D=5 Haar records (achieved/N_h ~ 0.87)."""
import math
TABLE = {  # DS14 v2 (2013) Table 4 = CombinatoricsWiki 10 March 2013; D=3 col updated by AL 2022 (see TABLE.md)
 3:[14,30,56,126,168,256,506,800], 4:[26,80,160,728,840,2184,4970,11748], 5:[42,170,336,2730,3110,9234,27936,90068],
 6:[62,312,684,7812,8310,29790,117360,452032], 7:[80,346,1134,8992,23436,80940,400160,1987380],
 8:[114,800,1710,39216,40586,201480,1091232,6927210], 9:[146,1170,2496,74898,117648,449480,2961536,20017260],
 10:[182,1640,4000,132860,224694,1176480,7057400,50331156], 11:[190,1734,5850,142464,398580,2246940,15200448,None],
 12:[266,2928,8200,354312,664300,4650100,30001152,300383050], 13:[270,3064,11480,374452,1062936,5314680,50990610,617330936],
 14:[366,4760,14760,804468,1771560,14172480,95087738,1213477190], 15:[370,4946,20496,842048,2480184,14172480,168016334,2300326510],
 16:[394,5134,27300,884062,4022340,36201060,288939118,4119507330]}
def moore(d, D): return 2*sum((d-1)**i for i in range(D))
def W(d, D):
    if D % 2: k=(D-1)//2; return 1+sum(d*(d-1)**(2*i-1) for i in range(1,k+1))
    k=D//2; return d*sum((d-1)**(2*i) for i in range(k))
def Nh(d, D):
    w=W(d,D); lo,hi=10.0,float(w)
    for _ in range(200):
        m=(lo+hi)/2
        if m*math.exp(-w/m) < d*math.log(m): lo=m
        else: hi=m
    return lo
if __name__=="__main__":
    rows=[]
    for d in range(3,17):
        for D in range(5,11):
            t=TABLE[d][D-3]
            if t is None: continue
            w=W(d,D); nh=Nh(d,D); pred=2*int(0.87*nh)
            rows.append((pred/t,d,D,t,moore(d,D),w,w/(t/2),int(nh),pred))
    rows.sort(reverse=True)
    print("pred/table  (Δ,D)  table  Moore  W  W/(table/2)  N_h  pred=2*0.87*N_h")
    for r in rows: print("%.2f (%d,%d) %d %d %d %.2f %d %d"%r)

import re,glob,math,sys
# best LPS order per (Delta, D) and comparison with the 2013 table / lab records (D=8..10 only for the table)
table={ (4,8):2184,(6,8):29790,(8,8):201480,(12,8):4650100,(14,8):14172480,
 (4,9):4970,(6,9):117360,(8,9):1091232,(12,9):30001152,(14,9):95087738,
 (4,10):11748,(6,10):452032,(8,10):6927210,(12,10):300383050,(14,10):1213477190,
 (4,7):840,(6,7):8310,(8,7):40586,(12,7):664300,(14,7):1771560,
 (4,6):1456,(6,6):7812,(8,6):39216,(12,6):354312,(14,6):804468}
rec={(6,8):31680,(8,8):239904,(6,9):127296,(8,9):1341600,(12,9):34026720,(14,9):116068656,(4,10):12416,(6,10):524160,(8,10):7818096,(12,10):325832976,(14,10):1326627120,(4,7):864,(6,7):8880,(8,7):43344}
def moore(d,D): return 2*sum((d-1)**j for j in range(D))
best={}
for f in sorted(glob.glob(sys.argv[1] if len(sys.argv)>1 else 'scan/lps_p*.txt')):
  for L in open(f):
    m=re.search(r'q=(\d+) m=(\d+) Delta=(\d+).*vertices=(\d+).*diameter=(\d+)',L)
    if not m: continue
    q,mm,d,n,D=map(int,m.groups())
    for DD in range(D,16):
      if n>best.get((d,DD),(0,))[0]: best[(d,DD)]=(n,q,D)
for (d,D) in sorted(best):
  n,q,DD=best[(d,D)]
  print(f"Delta={d:2d} D={D:2d} best LPS n={n:>10,} (q={q}, diam {DD})  {100*n/moore(d,D):5.2f}% of Moore  table={table.get((d,D),'-')} ours={rec.get((d,D),'-')}")

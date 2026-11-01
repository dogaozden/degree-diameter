import sys
P,K=101,25
S=[int(x) for x in sys.argv[2:]]
out=open(sys.argv[1],'w')
out.write(f"4 9 meta {P} {K} 5 n 1 N {P*K} cost 0\n")
for s in S:
    out.write(f"{s} meta(a={s//K},j={s%K}) z=0\n")
out.close()

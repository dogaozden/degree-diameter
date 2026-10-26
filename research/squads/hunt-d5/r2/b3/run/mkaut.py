# One GAP call per group: multiplication table + automorphism class reps of orders 2,3,4,6 (same format as gapgroup.py table).
import sys, os, struct
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hunt-d5/tools')
import gapgroup as gg
n, i, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
KS = [2, 3, 4, 6]
tmp = out + '.txt'
code = f'''G:=SmallGroup({n},{i});; el:=AsSSortedList(G);; one:=One(G);; p:=Position(el,one);;
el:=Concatenation([one], el{{Difference([1..Length(el)],[p])}});;
srt:=SortingPerm(el);; sel:=AsSSortedList(el);;
pos:=function(x) return Position(sel,x)^srt; end;;
PrintTo("{tmp}","");; f:=OutputTextFile("{tmp}",false);; SetPrintFormattingStatus(f,false);;
for x in el do AppendTo(f, JoinStringsWithSeparator(List(el, y->String(pos(x*y)-1)), " "), "\\n"); od;
CloseStream(f);;
A:=AutomorphismGroup(G);; cl:=ConjugacyClasses(A);;
'''
for k in KS:
    code += f'''res:=[];; for c in cl do a:=Representative(c); if Order(a)={k} then
  im:=List(el, x->pos(Image(a,x))-1); nf:=Number([1..Length(el)], j->im[j]=j-1); Add(res,[nf,im]); fi; od;
Sort(res, function(u,v) return u[1]<v[1]; end);;
g:=OutputTextFile("{out}.aut{k}",false);; SetPrintFormattingStatus(g,false);;
for r in res do AppendTo(g, String(r[1]), " ", JoinStringsWithSeparator(List(r[2],String)," "), "\\n"); od; CloseStream(g);;
'''
gg.rungap(code)
rows = [list(map(int, l.split())) for l in open(tmp)]
os.unlink(tmp)
assert len(rows) == n and all(len(r) == n for r in rows)
with open(out, 'wb') as f:
    f.write(struct.pack('<i', n))
    for r in rows: f.write(struct.pack('<%dH' % n, *r))
for k in KS:
    print(out + '.aut%d' % k, sum(1 for _ in open(out + '.aut%d' % k)) if os.path.exists(out + '.aut%d' % k) else 'MISSING')

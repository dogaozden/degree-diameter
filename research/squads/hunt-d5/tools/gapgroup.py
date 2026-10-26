#!/usr/bin/env python3
"""Export GAP SmallGroups as multiplication tables (+ optional automorphisms) for the hunt-d5 tools.

Usage: python3 gapgroup.py list N                 one line per group of order N: "N i abelian? |G'| |Z| structure"
       python3 gapgroup.py orbits N I             one element index per Aut(G)-orbit on G minus e, with orbit sizes
       python3 gapgroup.py table N I OUT.bin [K]  table of SmallGroup(N,I) -> OUT.bin (int32 N, N*N uint16, row g: g*h,
                                                  identity = index 0); with K: also OUT.aut<K> listing automorphisms of
                                                  order K (one class rep per Aut-conjugacy class, fewest fixed points
                                                  first): each line "nfix p0 p1 ... p_{N-1}" (image of element j)
GAP: the passagemath-gap wheel (pip install passagemath-gap); binary below.
"""
import os, struct, subprocess, sys, tempfile
GAP = '/usr/local/lib/python3.13/dist-packages/sage_wheels/bin/gap'

def rungap(code, timeout=3600):
    with tempfile.NamedTemporaryFile('w', suffix='.g', delete=False) as f:
        f.write(code + '\nQUIT;\n'); fn = f.name
    r = subprocess.run([GAP, '-q', '-o', '8g', fn], capture_output=True, text=True, timeout=timeout)
    os.unlink(fn)
    if r.returncode != 0: sys.stderr.write(r.stderr)
    return r.stdout

def glist(n):
    code = f'''for i in [1..NrSmallGroups({n})] do G:=SmallGroup({n},i);
Print({n}," ",i," ",IsAbelian(G)," ",Size(DerivedSubgroup(G))," ",Size(Centre(G))," \\"",StructureDescription(G),"\\"\\n"); od;'''
    sys.stdout.write(rungap(code))

def table(n, i, out, k=None):
    tmp = out + '.txt'
    code = f'''G:=SmallGroup({n},{i});; el:=AsSSortedList(G);; one:=One(G);; p:=Position(el,one);;
el:=Concatenation([one], el{{Difference([1..Length(el)],[p])}});;
srt:=SortingPerm(el);; sel:=AsSSortedList(el);;
pos:=function(x) return Position(sel,x)^srt; end;;
PrintTo("{tmp}","");; f:=OutputTextFile("{tmp}",false);; SetPrintFormattingStatus(f,false);;
for x in el do AppendTo(f, JoinStringsWithSeparator(List(el, y->String(pos(x*y)-1)), " "), "\\n"); od;
CloseStream(f);;
'''
    if k:
        code += f'''A:=AutomorphismGroup(G);; cl:=ConjugacyClasses(A);; res:=[];;
for c in cl do a:=Representative(c); if Order(a)={k} then
  im:=List(el, x->pos(Image(a,x))-1); nf:=Number([1..Length(el)], j->im[j]=j-1); Add(res,[nf,im]); fi; od;
Sort(res, function(u,v) return u[1]<v[1]; end);;
g:=OutputTextFile("{out}.aut{k}",false);; SetPrintFormattingStatus(g,false);;
for r in res do AppendTo(g, String(r[1]), " ", JoinStringsWithSeparator(List(r[2],String)," "), "\\n"); od; CloseStream(g);;
'''
    rungap(code)
    rows = [list(map(int, l.split())) for l in open(tmp)]
    os.unlink(tmp)
    assert len(rows) == n and all(len(r) == n for r in rows)
    with open(out, 'wb') as f:
        f.write(struct.pack('<i', n))
        for r in rows: f.write(struct.pack('<%dH' % n, *r))

def orbits(n, i):
    """one representative (table index) per orbit of Aut(G) on G minus the identity, with the orbit size"""
    code = f'''G:=SmallGroup({n},{i});; el:=AsSSortedList(G);; one:=One(G);; p:=Position(el,one);;
el:=Concatenation([one], el{{Difference([1..Length(el)],[p])}});;
srt:=SortingPerm(el);; sel:=AsSSortedList(el);; pos:=function(x) return Position(sel,x)^srt; end;;
A:=AutomorphismGroup(G);; O:=Orbits(A, el{{[2..Length(el)]}});;
for o in O do Print(Minimum(List(o, x->pos(x)-1)), " ", Length(o), "\\n"); od;'''
    sys.stdout.write(rungap(code))

if __name__ == '__main__':
    if sys.argv[1] == 'list': glist(int(sys.argv[2]))
    elif sys.argv[1] == 'orbits': orbits(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == 'table':
        table(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5]) if len(sys.argv) > 5 else None)

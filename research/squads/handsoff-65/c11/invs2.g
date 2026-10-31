# usage: gap -q -c 'ORDER:=176; ID:=17; OUTDIR:="invs2";' invs2.g
# One representative per Aut(G)-conjugacy class of involutory automorphisms theta (incl. identity); writes f = inv o theta
# as m integers to OUTDIR/c_ORDER_ID_k.map (one line), and OUTDIR/c_ORDER_ID.sum with k, |class|, #fixed points.
G := SmallGroup(ORDER, ID);
el := Elements(G);
e := Position(el, One(G));
el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
A := AutomorphismGroup(G);
cls := ConjugacyClasses(A);
sumf := OutputTextFile(Concatenation(OUTDIR, "/c_", String(ORDER), "_", String(ID), ".sum"), false);
SetPrintFormattingStatus(sumf, false);
AppendTo(sumf, "# |Aut|=", Size(A), " classes=", Length(cls), "\n");
k := 0;
for c in cls do
  th := Representative(c);
  if not th^2 = One(A) then continue; fi;
  k := k + 1;
  f := List(el, g -> Position(el, Inverse(Image(th, g))) - 1);
  out := OutputTextFile(Concatenation(OUTDIR, "/c_", String(ORDER), "_", String(ID), "_", String(k), ".map"), false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, JoinStringsWithSeparator(f, " "), "\n");
  CloseStream(out);
  AppendTo(sumf, k, " size=", Size(c), " fixed=", Number([1..Length(f)], i -> f[i] = i - 1), "\n");
od;
CloseStream(sumf);
QUIT;

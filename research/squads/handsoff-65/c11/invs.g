# usage: gap -q -c 'ORDER:=176; ID:=17; OUTDIR:="invs";' invs.g
# For G = SmallGroup(ORDER, ID) (element order as in gap_tables.g): for every involutory automorphism theta
# (theta^2 = 1, including the identity) write f(g) = theta(g)^-1 as m integers (one line) to OUTDIR/f_ORDER_ID_k.map,
# and a summary line (k, #fixed points of f, is_identity) to OUTDIR/f_ORDER_ID.sum.
G := SmallGroup(ORDER, ID);
el := Elements(G);
e := Position(el, One(G));
el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
A := AutomorphismGroup(G);
inv := Filtered(Elements(A), x -> x^2 = One(A));
sumf := OutputTextFile(Concatenation(OUTDIR, "/f_", String(ORDER), "_", String(ID), ".sum"), false);
SetPrintFormattingStatus(sumf, false);
AppendTo(sumf, "# |Aut|=", Size(A), " involutory(incl id)=", Length(inv), "\n");
k := 0;
seen := [];
for th in inv do
  f := List(el, g -> Position(el, Inverse(Image(th, g))) - 1);
  if f in seen then continue; fi;
  Add(seen, f);
  k := k + 1;
  out := OutputTextFile(Concatenation(OUTDIR, "/f_", String(ORDER), "_", String(ID), "_", String(k), ".map"), false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, JoinStringsWithSeparator(f, " "), "\n");
  CloseStream(out);
  AppendTo(sumf, k, " fixed=", Number([1..Length(f)], i -> f[i] = i - 1), " identity=", f = [0..Length(f)-1], "\n");
od;
CloseStream(sumf);
QUIT;

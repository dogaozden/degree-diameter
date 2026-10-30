# usage: gap -q -c 'ORDER:=176; IDS:=[26]; OUTDIR:="alpha";' export_alpha.g
# For each SmallGroup(ORDER,i): every conjugacy class of automorphisms of order 3 or 4 (ORDS), exported as
# OUTDIR/al_<ORDER>_<i>_<k>.txt: line 1 "order classsize m", line 2 = alpha as a permutation of 0..m-1 in the
# gap_tables.g element order (identity index 0).
if not IsBound(ORDS) then ORDS := [3,4]; fi;
for i in IDS do
  G := SmallGroup(ORDER, i);
  el := Elements(G);
  e := Position(el, One(G));
  el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  A := AutomorphismGroup(G);
  cl := ConjugacyClasses(A);
  k := 0;
  for c in cl do
    f := Representative(c);
    o := Order(f);
    if o in ORDS then
      k := k + 1;
      perm := List(el, x -> Position(el, Image(f, x)) - 1);
      out := OutputTextFile(Concatenation(OUTDIR, "/al_", String(ORDER), "_", String(i), "_", String(k), ".txt"), false);
      SetPrintFormattingStatus(out, false);
      AppendTo(out, o, " ", Size(c), " ", Size(G), "\n");
      AppendTo(out, JoinStringsWithSeparator(perm, " "), "\n");
      CloseStream(out);
    fi;
  od;
  Print("group ", ORDER, " ", i, " ", StructureDescription(G), " |Aut|=", Size(A), " alpha classes exported=", k, "\n");
od;
QUIT;

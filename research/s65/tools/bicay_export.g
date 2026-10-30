# bicay_export.g: export groups G with an index-2 subgroup E (one per Aut(G)-class) for bicay.c.
# Usage: gap -q -c 'ORDER:=344; OUTDIR:="groups"; CAP:=20000;' bicay_export.g     (optional IDS:=[...];)
# Writes OUTDIR/bc_<ORDER>_<id>_<k>.txt:
#   line 1: m
#   m rows: multiplication table (row g, col h: index of g*h), element 0 = identity
#   1 row : parity of each element (0 = in E, 1 = outside E)
#   then: A, followed by A rows, each a permutation of 0..m-1 (automorphisms of G fixing E; a subgroup of Aut
#         when the full stabiliser is larger than CAP; A = 1 means only the identity)
# and OUTDIR/bc_<ORDER>_<id>_<k>.name with StructureDescription(G), StructureDescription(K), |Aut|, |A|, #involutions
# outside E.
if not IsBound(IDS) then IDS := [1..NrSmallGroups(ORDER)]; fi;
if not IsBound(CAP) then CAP := 20000; fi;
for id in IDS do
  G := SmallGroup(ORDER, id);
  if not IsAbelian(G) then
  idx2 := Filtered(NormalSubgroups(G), N -> Index(G, N) = 2);
  if Length(idx2) > 0 then
    Au := AutomorphismGroup(G);
    reps := [];
    for N in idx2 do
      if ForAll(reps, M -> RepresentativeAction(Au, M, N, function(X, a) return Image(a, X); end) = fail) then
        Add(reps, N);
      fi;
    od;
    el := Elements(G);
    e := Position(el, One(G));
    el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
    k := 0;
    for K in reps do
      k := k + 1;
      St := Stabilizer(Au, K, function(X, a) return Image(a, X); end);
      if Size(St) > CAP then
        Inn := Intersection(St, InnerAutomorphismsAutomorphismGroup(Au));
        if Size(Inn) > CAP then Inn := TrivialSubgroup(St); fi;
        St := Inn;
      fi;
      fn := Concatenation(OUTDIR, "/bc_", String(ORDER), "_", String(id), "_", String(k), ".txt");
      out := OutputTextFile(fn, false);
      SetPrintFormattingStatus(out, false);
      AppendTo(out, String(ORDER), "\n");
      mt := MultiplicationTable(el);
      for row in mt do
        AppendTo(out, JoinStringsWithSeparator(List(row, x -> String(x - 1)), " "), "\n");
      od;
      AppendTo(out, JoinStringsWithSeparator(List(el, g -> String(Number([g], x -> not x in K))), " "), "\n");
      AppendTo(out, String(Size(St)), "\n");
      for a in Elements(St) do
        AppendTo(out, JoinStringsWithSeparator(List(el, g -> String(Position(el, Image(a, g)) - 1)), " "), "\n");
      od;
      CloseStream(out);
      ninv := Number(el, g -> Order(g) = 2 and not g in K);
      PrintTo(Concatenation(OUTDIR, "/bc_", String(ORDER), "_", String(id), "_", String(k), ".name"),
              StructureDescription(G), " | E = ", StructureDescription(K), " | Aut ", Size(Au), " | A ", Size(St),
              " | odd involutions ", ninv, "\n");
    od;
  fi;
  fi;
od;
QUIT;

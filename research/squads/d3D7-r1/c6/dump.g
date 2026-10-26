# Dump every SmallGroup(n,i) as a 0-based multiplication table (identity = 0) plus
# the double-coset decompositions H1\G/H2 for H1=<a> (a = involution class rep) and
# H2=<b> (b ranging over N(<a>)-orbits of involutions).
Str := function(l)
  local s, x;
  s := "";
  for x in l do Append(s, String(x)); Append(s, " "); od;
  return s;
end;

DumpOrder := function(n, fn)
  local seen, g, out, i, G, S, E, posE, Idx, M, x, invs, rem, a, cl, N, orbs, orb, b, H1, H2, dcs, dc, nG, npairs;
  nG := NrSmallGroups(n);
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  for i in [1..nG] do
    G := SmallGroup(n, i);
    S := AsSortedList(G);
    E := Concatenation([One(G)], Filtered(S, x -> x <> One(G)));
    posE := List(S, x -> Position(E, x));
    Idx := function(y) return posE[PositionSorted(S, y)] - 1; end;
    M := List([1..n], x -> List([1..n], y -> Idx(E[x]*E[y])));
    WriteLine(out, Concatenation("GROUP ", String(n), " ", String(i)));
    for x in [1..n] do WriteLine(out, Str(M[x])); od;
    invs := Filtered(E, x -> x <> One(G) and x^2 = One(G));
    rem := ShallowCopy(invs);
    while Length(rem) > 0 do
      a := rem[1];
      cl := ConjugacyClass(G, a);
      rem := Difference(rem, AsList(cl));
      N := Normalizer(G, Group(a));
      orbs := Orbits(N, invs, {x,g} -> x^g);
      H1 := Group(a);
      for orb in orbs do
        b := orb[1];
        H2 := Group(b);
        dcs := [];
        seen := [];
        for g in E do
          if not g in seen then
            dc := Set(Flat(List(Elements(H1), h -> List(Elements(H2), k -> h*g*k))));
            Append(seen, dc);
            Add(dcs, dc);
          fi;
        od;
        WriteLine(out, Concatenation("PAIR ", String(Idx(a)), " ", String(Idx(b)), " ", String(Length(dcs))));
        for dc in dcs do
          WriteLine(out, Concatenation(String(Length(dc)), " ", Str(List(dc, Idx))));
        od;
      od;
    od;
  od;
  CloseStream(out);
end;

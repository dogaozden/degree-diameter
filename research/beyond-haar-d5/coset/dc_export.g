# Bi-coset graphs of a group G on the right cosets of H (side A) and K (side B), |H| = |K| = h.
# Hx ~ Ky iff x y^-1 in S, S a union of double cosets H g K. For each double coset D = H g K this writes the
# edge list of the graph with S = D (A-point index, B-point index), so that any union can be assembled.
# Usage: gap -q -c 'GNAME:="PSL(2,13)"; G:=PSL(2,13); H_ORDER:=6; OUT:="out/psl2_13_h6";' dc_export.g
# Writes OUT_<i>_<j>.dc for every pair (H class i, K class j), j >= i: header "nA nB ndc", then per double coset a
# line "contrib nedges" followed by the edges "a b".
Hs := List(Filtered(ConjugacyClassesSubgroups(G), c -> Size(Representative(c)) = H_ORDER), Representative);
Hs := Filtered(Hs, H -> Size(Core(G, H)) = 1);   # nontrivial core: a graph of G/core (normal H: Haar of G/H)
Print(GNAME, ": ", Length(Hs), " classes of subgroups of order ", H_ORDER, "\n");
for i in [1..Length(Hs)] do for j in [i..Length(Hs)] do
  H := Hs[i]; K := Hs[j];
  RA := RightTransversal(G, H); RB := RightTransversal(G, K);
  nA := Length(RA); nB := Length(RB);
  dcs := DoubleCosets(G, H, K);
  fn := Concatenation(OUT, "_", String(i), "_", String(j), ".dc");
  out := OutputTextFile(fn, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, nA, " ", nB, " ", Length(dcs), "\n");
  for D in dcs do
    # edges of S = D: for each A-coset H x (x in RA), B-cosets K y with x y^-1 in D, i.e. y in D^-1 x
    g := Representative(D);
    # B-cosets adjacent to H*1: K y with y^-1 in D  <=>  y in K g^-1 H; as cosets: {K g^-1 h : h in H}
    base := Set(List(Elements(H), hh -> PositionCanonical(RB, g^-1 * hh)));
    contrib := Length(base);
    AppendTo(out, contrib, " ", nA * contrib, "\n");
    for a in [1..nA] do
      x := RA[a];
      for bb in base do
        AppendTo(out, a - 1, " ", PositionCanonical(RB, RB[bb] * x) - 1, "\n");
      od;
    od;
  od;
  CloseStream(out);
  Print("  pair ", i, " ", j, ": nA ", nA, " double cosets ", Length(dcs), " contributions ",
        Collected(List(dcs, D -> Size(D) / Size(K))), "\n");
od; od;
QUIT;

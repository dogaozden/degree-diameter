# export4.g (own-small r2 card q1): fast export of SmallGroup multiplication tables by pc-exponent indexing.
# Input variables set by the caller: DIR (directory with trailing slash), ORD (list of orders, already filtered).
# Pass 1 writes non-abelian groups, pass 2 abelian ones. Each group goes to DIR/N_id.txt (one gap_export block,
# "G N id name" + N rows; row a, column b = index of el[a]*el[b], identity index 0), then DIR/manifest.txt gets "N id ab".
ExportOne := function(N, id, ab, DIR)
  local G, P, rel, L, w, s, i, k, e, el, idx, fn, out, nm, a, T;
  G := SmallGroup(N, id);
  P := Pcgs(G);
  rel := RelativeOrders(P);
  L := Length(rel);
  w := [];
  s := 1;
  for i in [1..L] do w[i] := s; s := s * rel[i]; od;
  el := [];
  for k in [0..N-1] do
    e := [];
    for i in [1..L] do e[i] := (QuoInt(k, w[i]) mod rel[i]); od;
    el[k+1] := PcElementByExponents(P, e);
  od;
  idx := function(g)
    local ee, t, j;
    ee := ExponentsOfPcElement(P, g);
    t := 0;
    for j in [1..L] do t := t + ee[j]*w[j]; od;
    return t;
  end;
  fn := Concatenation(DIR, String(N), "_", String(id), ".txt");
  out := OutputTextFile(Concatenation(fn, ".tmp"), false);
  SetPrintFormattingStatus(out, false);
  nm := Concatenation("SG", String(N), "_", String(id));
  if ab then nm := Concatenation(nm, "ab"); else nm := Concatenation(nm, "nab"); fi;
  WriteAll(out, Concatenation("G ", String(N), " ", String(id), " ", nm, "\n"));
  for a in [1..N] do
    T := List([1..N], b -> idx(el[a]*el[b]));
    WriteAll(out, Concatenation(JoinStringsWithSeparator(List(T, String), " "), "\n"));
  od;
  CloseStream(out);
  Exec(Concatenation("mv ", fn, ".tmp ", fn));
  if ab then AppendTo(Concatenation(DIR, "manifest.txt"), N, " ", id, " ab\n");
  else AppendTo(Concatenation(DIR, "manifest.txt"), N, " ", id, " nab\n"); fi;
end;

for pss in [false, true] do
  for N in ORD do
    for id in [1..NrSmallGroups(N)] do
      if IsAbelian(SmallGroup(N, id)) = pss then
        ExportOne(N, id, pss, DIR);
      fi;
    od;
  od;
od;

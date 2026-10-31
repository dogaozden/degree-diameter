# export_bc.g: write bi-Cayley group files for bicay_tabu.c.
# File format: m; m rows of the multiplication table (row g, column h: index of g*h, element 0 = identity);
# one row of parities (0 = in the index-2 subgroup K, 1 = outside K). No automorphism data.
# Usage: cd c5 && /tmp/claude-0/bin/gap -q -c 'ORDER:=352; OUTDIR:="groups";' export_bc.g
# (ORDER nonabelian groups; or MODE:="direct" with DIRECT:=some group constructor result in G)
ExportOne := function(G, K, fn)
  local el, e, mt, out, row;
  el := Elements(G);
  e := Position(el, One(G));
  el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  mt := MultiplicationTable(el);
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(Size(G)), "\n");
  for row in mt do
    AppendTo(out, JoinStringsWithSeparator(List(row, x -> String(x - 1)), " "), "\n");
  od;
  AppendTo(out, JoinStringsWithSeparator(List(el, g -> String(Number([g], x -> not x in K))), " "), "\n");
  CloseStream(out);
end;
if not IsBound(MODE) then MODE := "ids"; fi;
if MODE = "direct" then
  G := DirectProduct(SymmetricGroup(3), DihedralGroup(30));
  k := 0;
  for K in Filtered(NormalSubgroups(G), N -> Index(G, N) = 2) do
    k := k + 1;
    ExportOne(G, K, Concatenation(OUTDIR, "/s3d30_", String(k), ".txt"));
    PrintTo(Concatenation(OUTDIR, "/s3d30_", String(k), ".name"), StructureDescription(K), "\n");
  od;
  Print("exported ", k, " index-2 subgroups of S3xD30\n");
else
  for id in IDS do
    G := SmallGroup(ORDER, id);
    if not IsAbelian(G) then
      seen := [];
      k := 0;
      for K in Filtered(NormalSubgroups(G), N -> Index(G, N) = 2) do
        ik := IdGroup(K);
        if not ik in seen then
          Add(seen, ik);
          k := k + 1;
          fn := Concatenation(OUTDIR, "/g", String(ORDER), "_", String(id), "_", String(k), ".txt");
          ExportOne(G, K, fn);
          PrintTo(Concatenation(OUTDIR, "/g", String(ORDER), "_", String(id), "_", String(k), ".name"),
                  StructureDescription(G), " | K = ", StructureDescription(K), "\n");
        fi;
      od;
    fi;
  od;
fi;
QUIT;

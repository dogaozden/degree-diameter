# writes grp/<name>.txt multiplication tables (element 0 = identity), same format as gap_tables.g
WriteTable := function(G, name)
  local el, e, fn, out, g;
  el := Elements(G);
  e := Position(el, One(G));
  el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  fn := Concatenation("grp/", name, ".txt");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(Size(G)), "\n");
  for g in el do
    AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n");
  od;
  CloseStream(out);
  return Size(G);
end;
WriteTable(DirectProduct(ElementaryAbelianGroup(64), CyclicGroup(5)), "sg_320_C2^6xC5");
WriteTable(DirectProduct(DihedralGroup(64), CyclicGroup(5)), "sg_320_D64xC5");
QUIT;

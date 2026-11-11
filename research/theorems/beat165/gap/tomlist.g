LoadPackage("tomlib");
names := AllLibTomNames();
Print(Length(names), " tables\n");
res := [];
for nm in names do
  t := TableOfMarks(nm);
  if t <> fail then
    o := OrdersTom(t);
    sz := o[Length(o)];
    if sz >= 10^5 then Add(res, [sz, nm, Length(o)]); fi;
  fi;
od;
Sort(res);
for r in res do Print(r[1], " ", r[2], " classes=", r[3], "\n"); od;
QUIT;

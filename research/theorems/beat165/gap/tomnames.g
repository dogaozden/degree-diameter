LoadPackage("tomlib");
names := AllLibTomNames();
for nm in names do
  t := TableOfMarks(nm);
  if t <> fail then o := OrdersTom(t); sz := o[Length(o)];
    if sz >= 2*10^6 then Print(nm, " ", sz, " ", Length(o), "\n"); fi;
  fi;
od;
QUIT;

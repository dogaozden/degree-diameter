out := OutputTextFile("inv192.txt", false); SetPrintFormattingStatus(out, false);
for i in [1..NrSmallGroups(192)] do G := SmallGroup(192, i);
  if not IsAbelian(G) then k := Sum(Filtered(ConjugacyClasses(G), c -> Order(Representative(c)) = 2), Size);
    if k <= 3 then AppendTo(out, i, " ", k, " ", StructureDescription(G), "\n"); fi; fi; od;
CloseStream(out); QUIT;

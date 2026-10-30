out := OutputTextFile("inv128.txt", false); SetPrintFormattingStatus(out, false);
for i in [1..NrSmallGroups(128)] do P := SmallGroup(128, i);
  if not IsAbelian(P) then k := Sum(Filtered(ConjugacyClasses(P), c -> Order(Representative(c)) = 2), Size);
    if k <= 11 then AppendTo(out, i, " ", k, "\n"); fi; fi; od;
CloseStream(out); QUIT;

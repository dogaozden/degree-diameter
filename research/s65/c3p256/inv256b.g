out := OutputTextFile("inv256_12_23.txt", false); SetPrintFormattingStatus(out, false);
for i in [1..26245] do P := SmallGroup(256, i);
  if not IsAbelian(P) then k := Sum(Filtered(ConjugacyClasses(P), c -> Order(Representative(c)) = 2), Size);
    if k >= 12 and k <= 23 then AppendTo(out, i, " ", k, "\n"); fi; fi; od;
CloseStream(out); QUIT;

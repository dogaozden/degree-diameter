tot := 0;
for n in [661..720] do
  Print(n, ":", NrSmallGroups(n), " ");
  tot := tot + NrSmallGroups(n);
od;
Print("\nTOTAL ", tot, "\n");
QUIT;

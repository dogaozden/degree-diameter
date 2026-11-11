L := Filtered([2531..2600], n -> not SmallGroupsAvailable(n));
Print("NOTAVAIL ", L, "\n");
Print("AVAIL ", Filtered([2531..2600], n -> SmallGroupsAvailable(n)), "\n");
QUIT;

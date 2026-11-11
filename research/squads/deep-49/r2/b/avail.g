for n in [1992..2100] do if n mod 4 = 0 and SmallGroupsAvailable(n) then Print("H ", n, " ", NrSmallGroups(n), "\n"); fi; od;
for n in [2486..2600] do if SmallGroupsAvailable(n) then Print("M ", n, " ", NrSmallGroups(n), "\n"); fi; od;
QUIT;

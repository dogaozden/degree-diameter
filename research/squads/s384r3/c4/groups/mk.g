LIST := [];
for N in [172,174,178,182,184,186,188,190] do
  for i in [1..NrSmallGroups(N)] do
    if not IsAbelian(SmallGroup(N,i)) then Add(LIST, [N,i]); fi;
  od;
od;
nonab := Filtered([1..NrSmallGroups(192)], i -> not IsAbelian(SmallGroup(192,i)));
for k in [1..6] do Add(LIST, [192, nonab[Int(k*Length(nonab)/7)]]); od;
PrintTo("groups/list.txt", "");
for pr in LIST do AppendTo("groups/list.txt", pr[1], " ", pr[2], "\n"); od;
Print(Length(LIST), "\n");
QUIT;

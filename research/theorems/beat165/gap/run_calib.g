Read("cosetsearch.g");
log := "calib.log";
PrintTo(log, "calibration: D<=5 coset graphs with max degree <= 16\n");
for nm in ["L3(4)", "U3(4)", "U3(5)", "L3(5)", "M22", "J2", "S4(4)", "A9", "M12", "L2(64)", "L2(81)", "S6(2)", "A10", "L3(7)", "U4(3)", "G2(3)", "S4(5)", "U3(8)", "U3(7)", "L4(3)"] do
  SearchTom(nm, 16, 9, 1000, 54241, 4000, log);
od;
QUIT;

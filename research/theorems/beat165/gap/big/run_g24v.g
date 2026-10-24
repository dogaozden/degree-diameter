VERBOSE := true;
Read("cosetsearch2.g");
log := "big/G2_4_verbose.log"; PrintTo(log, "");
SearchTom2("G2(4)", 16, 9, 4000, 54241, 10000, log);
QUIT;

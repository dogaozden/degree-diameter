#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c2
printf '%s\n' "7|cyc_49|cyc_49|bases/heawood_m6_s1.txt|120|201" "7|cyc_49|cyc_49|bases/rand_h7_s1.txt|120|202" "7|cyc_49|cyc_49|bases/K77_minus_pm.txt|120|203" "7|z7xz7|cyc_7_x_cyc_7|bases/heawood_m6_s1.txt|120|204" "7|z7xz7|cyc_7_x_cyc_7|bases/rand_h7_s1.txt|120|205" "7|z7xz7|cyc_7_x_cyc_7|bases/K77_minus_pm.txt|120|206" | xargs -P 2 -I{} ./run_one.sh {}
echo done > long_done.flag

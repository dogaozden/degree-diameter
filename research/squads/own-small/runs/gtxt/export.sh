#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/runs/gtxt
sed 's#"groups/g"#"/home/user/degree-diameter/research/squads/own-small/runs/gtxt/g"#' ../../tools/gap_export.g > exp.g
echo 'lo:=51;; hi:=66;; Read("exp.g");' | nice -n 5 gap -q -o 4g > exp1.log 2>&1
echo 'lo:=101;; hi:=125;; Read("exp.g");' | nice -n 5 gap -q -o 4g > exp2.log 2>&1
echo EXPORTED > exported

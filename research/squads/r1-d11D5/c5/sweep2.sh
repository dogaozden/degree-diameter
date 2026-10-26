#!/bin/bash
cd /home/user/degree-diameter/research/squads/r1-d11D5/c5
./c5g Z 14 1 20000 16 60 > hot_Z14_s1.txt 2>&1
./c5g D 14 1 20000 16 60 > hot_D14_s1.txt 2>&1
./c5g Z 10 1 20000 16 60 > hot_Z10_s1.txt 2>&1
./c5g Z 8 1 20000 16 60 > hot_Z8_s1.txt 2>&1
echo DONE > sweep2.done

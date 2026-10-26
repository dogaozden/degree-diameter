#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/r1/b1
./orb base_tree.txt groups/Z7.txt sigma7.perm - 150 5 g_z7s7 1000 10 2> g_z7s7.log
./orb base_tree.txt groups/Z2^3.txt sigma7.perm phi7_Z2^3.txt 150 5 g_z2s7 1000 10 2> g_z2s7.log

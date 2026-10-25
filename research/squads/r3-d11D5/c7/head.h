/* orb.c: H-equivariant annealer for a DM base (card c7). Cost = exact total() of plusopt7.c (copied below).
   Moves are H-orbit moves: sigma swaps on whole orbits, degree-preserving flag swaps applied to all images.
   usage: SECS=600 SEED=1 T0=20 T1=0.5 PF=0.3 PH=0.7 OUT=best.in OUT0=fail0.in ./orb start.in group.grp */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

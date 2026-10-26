# Building Weyl-distance graphs with max degree 6: any diameter-5 member above 600 vertices? (job fresh-6-5)
import sys
sys.argv = ['weyl_graphs.py', 'none']
import weyl_graphs as W
W.scan(maxdeg=6, minorder=500, maxD=5, show_near=7)

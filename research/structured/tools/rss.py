"""rss.py CMD...: run CMD, then print its peak resident memory (ru_maxrss of the children) to stderr."""
import sys, subprocess, resource
r = subprocess.call(sys.argv[1:])
sys.stderr.write('maxrss_MB %.0f\n' % (resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)); sys.exit(r)

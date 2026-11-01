import subprocess, sys, resource, os
env=dict(os.environ, THREADS="1")
cmd=sys.argv[1:]
p=subprocess.run(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
out=p.stdout.splitlines()
for l in out[-12:]: print(l[:300])
print("RC", p.returncode, "MAXRSS_MB", resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss/1024)

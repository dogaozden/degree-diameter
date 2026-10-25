#!/usr/bin/env python3
"""B4 helper: run one command, timestamp every output line, report wall time and peak RSS.

Usage (run with -I, inside gate.sh):  python3 -I runtimed.py LOG CMD [ARGS...]
Writes LOG with lines "[  12.34s] <output line>" and a final line "RUNTIMED wall=.. user=.. sys=.. maxrss_MB=.. rc=..".
On SIGTERM/SIGINT (for example from `timeout`) the whole child process group is killed, so nothing is left running.
"""
import os
import signal
import subprocess
import sys
import time

log_path, cmd = sys.argv[1], sys.argv[2:]
log = open(log_path, "w", buffering=1)
child = None


def kill_all(signum, frame):
    hwm = "?"
    if child is not None:
        try:
            with open("/proc/%d/status" % child.pid) as st:
                hwm = [l.split()[1] for l in st if l.startswith("VmHWM")][0]
        except (OSError, IndexError):
            pass
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    log.write("RUNTIMED killed by signal %d after %.2fs wall, peak VmHWM=%s kB (child killed)\n"
              % (signum, time.time() - t0, hwm))
    log.close()
    os._exit(124)


signal.signal(signal.SIGTERM, kill_all)
signal.signal(signal.SIGINT, kill_all)

t0 = time.time()
child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1,
                         start_new_session=True)
for line in child.stdout:
    log.write("[%7.2fs] %s" % (time.time() - t0, line if line.endswith("\n") else line + "\n"))
_, status, ru = os.wait4(child.pid, 0)
wall = time.time() - t0
rc = os.waitstatus_to_exitcode(status)
log.write("RUNTIMED wall=%.2fs user=%.2fs sys=%.2fs maxrss_MB=%.0f rc=%d cmd=%s\n"
          % (wall, ru.ru_utime, ru.ru_stime, ru.ru_maxrss / 1024.0, rc, " ".join(cmd[:1])))
log.close()
sys.exit(0 if rc == 0 else 1)

"""c7 watcher: at 05:00:00 UTC stops the base loop (run_loop2.sh) and its lscreen/lanneal children, then runs finish.py."""
import calendar
import os
import signal
import subprocess
import time
import sys
C7 = '/home/user/degree-diameter/research/squads/r2-smallfam/c7'
KILL_AT = calendar.timegm(time.strptime('2026-10-25 05:00:00', '%Y-%m-%d %H:%M:%S'))
while time.time() < KILL_AT:
    time.sleep(3)
PATS = (f'/bin/bash {C7}/run_loop2.sh', f'timeout 1200 nice -n 10 python3 {C7}/fastscreen.py',
        f'python3 {C7}/fastscreen.py', f'/home/user/degree-diameter/research/theorems/smallfam/lanneal {C7}/tmp/scr_tab_')
killed = []
for pid in os.listdir('/proc'):
    if not pid.isdigit() or int(pid) == os.getpid():
        continue
    try:
        cmd = open(f'/proc/{pid}/cmdline', 'rb').read().replace(b'\0', b' ').decode(errors='replace')
    except OSError:
        continue
    if cmd.startswith(PATS):
        os.kill(int(pid), signal.SIGTERM)
        killed.append((pid, cmd[:60]))
time.sleep(2)
print('killed at', time.strftime('%H:%M:%S', time.gmtime()), killed, flush=True)
subprocess.run(['python3', f'{C7}/finish.py'], cwd=C7)

/* gen3 N p3 p4 m < TEMPLATE : each template line holds m volts; positions p3, p4 are replaced by every pair
   (x, y) in [0,N)^2 and one line per (template, x, y) is written (input for flift eval). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static char out[1 << 22]; static size_t on = 0;
static void flush_out(void) { fwrite(out, 1, on, stdout); on = 0; }
static void put_int(int x) { char t[12]; int n = 0; do { t[n++] = '0' + x % 10; x /= 10; } while (x); while (n) out[on++] = t[--n]; }
int main(int argc, char **argv) {
    int N = atoi(argv[1]), p3 = atoi(argv[2]), p4 = atoi(argv[3]), m = atoi(argv[4]);
    static char buf[1 << 16]; int v[64];
    while (fgets(buf, sizeof buf, stdin)) {
        char *p = buf; int i = 0;
        for (; i < m; i++) { char *q; long x = strtol(p, &q, 10); if (q == p) break; v[i] = (int)x; p = q; }
        if (i < m) continue;
        for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) {
            v[p3] = x; v[p4] = y;
            for (int k = 0; k < m; k++) { put_int(v[k]); out[on++] = (k + 1 < m) ? ' ' : '\n'; }
            if (on > sizeof out - 256) flush_out();
        }
    }
    flush_out();
    return 0;
}

#include <math.h>
#include "j0fast.h"
#include "j0_table.h"
static inline double j0_asym(double x) {
  double z = 1.0 / x, z2 = z * z;
  double P = 1.0 - z2 * (9.0 / 128.0) + z2 * z2 * (3675.0 / 32768.0);
  double Q = z * (-1.0 / 8.0) + z * z2 * (75.0 / 1024.0);
  double ch = x - 0.78539816339744830962;
  return sqrt(0.63661977236758134308 * z) * (P * cos(ch) - Q * sin(ch));
}
static inline double j0_tab(double x) {
  double s = x * 8.0; long k = (long)s; double u = (s - (double)k) * 2.0 - 1.0;
  const double *c = J0T[k];
  double p = c[8];
  p = fma(p, u, c[7]); p = fma(p, u, c[6]); p = fma(p, u, c[5]); p = fma(p, u, c[4]);
  p = fma(p, u, c[3]); p = fma(p, u, c[2]); p = fma(p, u, c[1]); p = fma(p, u, c[0]);
  return p;
}
double j0f(double x) {
  if (x < 0) x = -x;
  return x < 1024.0 ? j0_tab(x) : j0_asym(x);
}
void j0v(const double *x, double *y, long n) {
  for (long i = 0; i < n; i++) { double a = fabs(x[i]); y[i] = a < 1024.0 ? j0_tab(a) : j0_asym(a); }
}
void j0sum(const double *r, const double *c, int m, const double *t, double *out, long n) {
  for (long i = 0; i < n; i++) out[i] = 0.0;
  for (int k = 0; k < m; k++) {
    double rk = fabs(r[k]), ck = c[k];
    for (long i = 0; i < n; i++) { double a = rk * fabs(t[i]); out[i] += ck * (a < 1024.0 ? j0_tab(a) : j0_asym(a)); }
  }
}
#include <dispatch/dispatch.h>
// multithreaded j0sum over chunks of t (GCD); nthreads caps the parallelism
void j0sum_mt(const double *r, const double *c, int m, const double *t, double *out, long n, int nthreads) {
  if (nthreads < 2 || n < 65536) { j0sum(r, c, m, t, out, n); return; }
  long chunk = (n + nthreads - 1) / nthreads;
  dispatch_apply((size_t)nthreads, dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^(size_t w) {
    long lo = (long)w * chunk, hi = lo + chunk < n ? lo + chunk : n;
    if (lo < hi) j0sum(r, c, m, t + lo, out + lo, hi - lo);
  });
}

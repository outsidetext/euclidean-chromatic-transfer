// Independent numeric evaluation of p = P(x, x+u same colour) for a periodic polygon colouring.
// Input (stdin): b1x b1y b2x b2y \n  npoly \n  for each: col nv x1 y1 ... \n
// Usage: pmono NTHETA   -> prints overlap check and p (trapezoid over theta in [0,pi), periodic integrand).
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#define MAXV 64
typedef struct { int n, col; double x[MAXV], y[MAXV], cx, cy, r; } Poly;
static double area(int n, const double *x, const double *y) {
  double a = 0; for (int i = 0; i < n; i++) { int j = (i + 1) % n; a += x[i] * y[j] - x[j] * y[i]; } return 0.5 * a; }
// clip subject polygon (sx,sy,sn) by convex CCW clip polygon; returns area of intersection
static double inter(const Poly *A, const Poly *B, double dx, double dy) {
  double px[2 * MAXV + 8], py[2 * MAXV + 8], qx[2 * MAXV + 8], qy[2 * MAXV + 8]; int pn = B->n;
  for (int i = 0; i < pn; i++) { px[i] = B->x[i] + dx; py[i] = B->y[i] + dy; }
  for (int e = 0; e < A->n && pn > 0; e++) {
    double ax = A->x[e], ay = A->y[e], bx = A->x[(e + 1) % A->n], by = A->y[(e + 1) % A->n];
    int qn = 0;
    for (int i = 0; i < pn; i++) {
      int j = (i + 1) % pn;
      double si = (bx - ax) * (py[i] - ay) - (by - ay) * (px[i] - ax);
      double sj = (bx - ax) * (py[j] - ay) - (by - ay) * (px[j] - ax);
      if (si >= 0) { qx[qn] = px[i]; qy[qn++] = py[i]; }
      if ((si >= 0) != (sj >= 0)) { double t = si / (si - sj); qx[qn] = px[i] + t * (px[j] - px[i]); qy[qn++] = py[i] + t * (py[j] - py[i]); }
    }
    pn = qn; for (int i = 0; i < pn; i++) { px[i] = qx[i]; py[i] = qy[i]; }
  }
  return pn >= 3 ? area(pn, px, py) : 0;
}
int main(int argc, char **argv) {
  int NT = argc > 1 ? atoi(argv[1]) : 2000;
  double b[4]; if (scanf("%lf %lf %lf %lf", b, b + 1, b + 2, b + 3) != 4) return 1;
  int np; scanf("%d", &np); Poly *P = calloc(np, sizeof(Poly));
  double tot = 0;
  for (int k = 0; k < np; k++) {
    scanf("%d %d", &P[k].col, &P[k].n);
    for (int i = 0; i < P[k].n; i++) scanf("%lf %lf", &P[k].x[i], &P[k].y[i]);
    double a = area(P[k].n, P[k].x, P[k].y);
    if (a < 0) { for (int i = 0; i < P[k].n / 2; i++) { int j = P[k].n - 1 - i; double t = P[k].x[i]; P[k].x[i] = P[k].x[j]; P[k].x[j] = t; t = P[k].y[i]; P[k].y[i] = P[k].y[j]; P[k].y[j] = t; } a = -a; }
    tot += a; double cx = 0, cy = 0; for (int i = 0; i < P[k].n; i++) { cx += P[k].x[i]; cy += P[k].y[i]; }
    P[k].cx = cx / P[k].n; P[k].cy = cy / P[k].n; P[k].r = 0;
    for (int i = 0; i < P[k].n; i++) { double r = hypot(P[k].x[i] - P[k].cx, P[k].y[i] - P[k].cy); if (r > P[k].r) P[k].r = r; }
  }
  double A = fabs(b[0] * b[3] - b[1] * b[2]);
  printf("polys %d  sum area %.12f  period area %.12f\n", np, tot, A);
  // candidate triples
  int cap = 1 << 20, nc = 0; int *ci = malloc(cap * sizeof(int)), *cj = malloc(cap * sizeof(int)); double *tx = malloc(cap * sizeof(double)), *ty = malloc(cap * sizeof(double));
  double overlap = 0;
  for (int i = 0; i < np; i++) for (int j = 0; j < np; j++) for (int m = -4; m <= 4; m++) for (int n = -4; n <= 4; n++) {
    double dx = m * b[0] + n * b[2], dy = m * b[1] + n * b[3];
    double d = hypot(P[j].cx + dx - P[i].cx, P[j].cy + dy - P[i].cy);
    if (d > P[i].r + P[j].r + 1.0 + 1e-9) continue;
    if (!(i == j && m == 0 && n == 0) && d < P[i].r + P[j].r) overlap += inter(&P[i], &P[j], dx, dy);
    if (P[i].col != P[j].col) continue;
    if (nc == cap) { cap *= 2; ci = realloc(ci, cap * sizeof(int)); cj = realloc(cj, cap * sizeof(int)); tx = realloc(tx, cap * sizeof(double)); ty = realloc(ty, cap * sizeof(double)); }
    ci[nc] = i; cj[nc] = j; tx[nc] = dx; ty[nc] = dy; nc++;
  }
  printf("float overlap area between distinct translates: %.3e\ncandidates %d\n", overlap, nc);
  fflush(stdout);
  double s = 0;
  for (int t = 0; t < NT; t++) {
    double th = M_PI * (t + 0.5) / NT, ux = cos(th), uy = sin(th), acc = 0;
    for (int k = 0; k < nc; k++) acc += inter(&P[ci[k]], &P[cj[k]], tx[k] + ux, ty[k] + uy);
    s += acc;
  }
  double p = s / NT / A;
  printf("NT %d  p = %.9f  1/p = %.5f\n", NT, p, 1 / p);
  return 0;
}

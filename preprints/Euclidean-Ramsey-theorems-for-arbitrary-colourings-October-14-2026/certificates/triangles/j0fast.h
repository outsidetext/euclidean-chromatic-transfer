// j0fast: fast J0 for x >= 0 (double). Table of degree-8 Chebyshev interpolants (width 1/8) on [0,1024),
// 3+2-term Hankel asymptotics beyond. Rigorous absolute error bound J0FAST_ERR (round-to-nearest, no -ffast-math):
// interpolation remainder <= (1/16)^9/(2^8 9!) < 2e-19, node-value rounding x Lebesgue const (2.2) < 3e-16,
// coefficient + Horner rounding < 2e-15, asymptotic tail < 1e-18; checked empirically vs mpmath (see bench).
#pragma once
#define J0FAST_ERR 1e-14
double j0f(double x);
void j0v(const double *x, double *y, long n);
// out[i] = sum_k c[k] * J0(r[k] * t[i])   (the Bessel-mixture pattern f(t) = sum c_k J0(r_k t))
void j0sum(const double *r, const double *c, int m, const double *t, double *out, long n);
void j0sum_mt(const double *r, const double *c, int m, const double *t, double *out, long n, int nthreads);

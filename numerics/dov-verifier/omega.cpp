
#include "omega.h"

using namespace std;


inline constexpr unsigned long factorial(unsigned long n)
{
    return n == 0 ? 1 : n * factorial(n - 1);
}


HalfIntegerBesselJ::HalfIntegerBesselJ(int n)
    : n{n}
{
    if (n < 0)
        throw invalid_argument{"n must be >= 0"};
    
    if (n == 0) {
        nsin_factors = 1;
        ncos_factors = 0;
        sin_factors = new mpfr_t[1];
        cos_factors = nullptr;
    }
    else {
        nsin_factors = 1 + n / 2;
        ncos_factors = 1 + (n - 1) / 2;
            
        sin_factors = new mpfr_t[nsin_factors];
        cos_factors = new mpfr_t[ncos_factors];
    }
    
    // factor = sqrt(2 / pi).
    mpfr_init(factor);
    mpfr_const_pi(factor, MPFR_RNDN);
    mpfr_ui_div(factor, 2, factor, MPFR_RNDN);
    mpfr_sqrt(factor, factor, MPFR_RNDN);

    // sin precomputed factors.
    int sign = 1;
    for (int k = 0; k < nsin_factors; k++, sign *= -1) {
        mpfr_init(sin_factors[k]);
        mpfr_set_si(sin_factors[k], sign * factorial(n + 2 * k),
                    MPFR_RNDN);
        mpfr_div_ui(sin_factors[k], sin_factors[k],
                    factorial(2 * k) * factorial(n - 2 * k),
                    MPFR_RNDN);
    }

    // cos precomputed factors.
    sign = 1;
    for (int k = 0; k < ncos_factors; k++, sign *= -1) {
        mpfr_init(cos_factors[k]);
        mpfr_set_si(cos_factors[k], sign * factorial(n + 2 * k + 1),
                    MPFR_RNDN);
        mpfr_div_ui(cos_factors[k], cos_factors[k],
                    factorial(2 * k + 1) * factorial(n - 2 * k - 1),
                    MPFR_RNDN);
    }

    mpfr_inits(arg, x, y, z, acc, nullptr);
}


HalfIntegerBesselJ::~HalfIntegerBesselJ()
{
    mpfr_clear(factor);

    for (int k = 0; k < nsin_factors; k++)
        mpfr_clear(sin_factors[k]);

    for (int k = 0; k < ncos_factors; k++)
        mpfr_clear(cos_factors[k]);

    delete[] sin_factors;
    delete[] cos_factors;
    
    mpfr_clears(arg, x, y, z, acc, nullptr);
}


void HalfIntegerBesselJ::eval(mpfr_t rop, mpfr_t op)
{
    if (rop == op)
        throw invalid_argument{"not implemented: rop = op"};
    
    // argument of sine or cosine.
    mpfr_const_pi(arg, MPFR_RNDN);
    mpfr_mul_ui(arg, arg, n, MPFR_RNDN);
    mpfr_div_ui(arg, arg, 2, MPFR_RNDN);
    mpfr_sub(arg, op, arg, MPFR_RNDN);

    // sin part.
    mpfr_set_ui(x, 1, MPFR_RNDN);       // x = 1
    mpfr_mul_ui(y, op, 2, MPFR_RNDN);   // y = 2 * op
    mpfr_mul(y, y, y, MPFR_RNDN);       // y = y * y = (2 * op)^2
    mpfr_set_ui(acc, 0, MPFR_RNDN);

    for (int k = 0; k < nsin_factors; k++) {
        mpfr_div(z, sin_factors[k], x, MPFR_RNDN);
        mpfr_add(acc, acc, z, MPFR_RNDN);
        mpfr_mul(x, x, y, MPFR_RNDN);
    }

    mpfr_sin(x, arg, MPFR_RNDN);
    mpfr_mul(rop, x, acc, MPFR_RNDN);

    // cos part.
    mpfr_mul_ui(x, op, 2, MPFR_RNDN);    // x = 2 * op
    mpfr_set_ui(acc, 0, MPFR_RNDN);

    for (int k = 0; k < ncos_factors; k++) {
        mpfr_div(z, cos_factors[k], x, MPFR_RNDN);
        mpfr_add(acc, acc, z, MPFR_RNDN);
        mpfr_mul(x, x, y, MPFR_RNDN);
    }

    mpfr_cos(x, arg, MPFR_RNDN);
    mpfr_mul(acc, acc, x, MPFR_RNDN);
    mpfr_add(rop, rop, acc, MPFR_RNDN);

    mpfr_sqrt(x, op, MPFR_RNDN);
    mpfr_div(rop, rop, x, MPFR_RNDN);
    mpfr_mul(rop, rop, factor, MPFR_RNDN);
}


OmegaFunc::OmegaFunc(int n)
    : n{n}
{
    if (n < 2)
        throw invalid_argument{"n must be >= 2"};

    if (n % 2 == 0)
        bessel_ptr.reset(new IntegerBesselJ{(n - 2) / 2});
    else
        bessel_ptr.reset(new HalfIntegerBesselJ{(n - 2) / 2});

    mpfr_inits(factor, p, nullptr);

    // Compute factor.
    mpfr_set_d(factor, n / 2.0, MPFR_RNDN);
    mpfr_gamma(factor, factor, MPFR_RNDN);
    mpfr_set_d(p, (n - 2) / 2.0, MPFR_RNDN);
    mpfr_ui_pow(p, 2, p, MPFR_RNDN);
    mpfr_mul(factor, factor, p, MPFR_RNDN);
}


void OmegaFunc::eval(mpfr_t rop, mpfr_t op)
{
    if (rop == op)
        throw invalid_argument{"not implemented: rop = op"};

    if (mpfr_zero_p(op)) {
        mpfr_set_ui(rop, 1, MPFR_RNDN);
        return;
    }    
    
    bessel_ptr->eval(rop, op);

    for (int k = 0; k < (n - 2) / 2; k++)
        mpfr_div(rop, rop, op, MPFR_RNDN);

    if (n % 2 != 0) {
        mpfr_sqrt(p, op, MPFR_RNDN);
        mpfr_div(rop, rop, p, MPFR_RNDN);
    }

    mpfr_mul(rop, rop, factor, MPFR_RNDN);
}

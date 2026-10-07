/*
  Omega_n function for verification of Euclidean space solutions.

  AUTHOR:

  - F.M. de Oliveira Filho <fmario@gmail.com>
*/

#ifndef __OMEGA_H__
#define __OMEGA_H__

#include <mpfr.h>
#include <memory>
#include <stdexcept>


// BesselJ function evaluator.
class BesselJ {
public:
    virtual ~BesselJ() { }

    virtual void eval(mpfr_t rop, mpfr_t op) = 0;
};


// Bessel function J_n for n >= 0 integer. This implementation simply
// uses MPFR.
class IntegerBesselJ : public BesselJ {
public:
    explicit IntegerBesselJ(int n) : n{n}
    {
        if (n < 0)
            throw std::invalid_argument{"n must be >= 0"};
    }
    
    void eval(mpfr_t rop, mpfr_t op)
    {
        mpfr_jn(rop, n, op, MPFR_RNDN);
    }
    
private:
    int n;
};


// Bessel function J_{n + 1/2} for n >= 0 integer. This is not thread
// safe.
class HalfIntegerBesselJ : public BesselJ {
public:
    explicit HalfIntegerBesselJ(int n);
    ~HalfIntegerBesselJ();

    // At the moment it is required to have rop != op. If rop == op
    // then an invalid_argument exception is thrown.
    void eval(mpfr_t rop, mpfr_t op);
    
private:
    const int n;
    mpfr_t factor;

    int nsin_factors, ncos_factors;
    mpfr_t *sin_factors, *cos_factors;

    mpfr_t arg, x, y, z, acc;
};


// Omega_n function.
class OmegaFunc {
public:
    explicit OmegaFunc(int n);
    ~OmegaFunc() { mpfr_clears(factor, p, nullptr); }

    // At the moment it is required to have rop != op. If rop == op
    // then an invalid_argument exception is thrown.
    void eval(mpfr_t rop, mpfr_t op);
    
private:
    int n;
    mpfr_t factor, p;
    std::unique_ptr<BesselJ> bessel_ptr;
};


#endif

// Local variables:
// mode: c++
// End:

/*
  This program verifies a dual solution of the optimization problem
  that provides an upper bound for the independence density of the
  unit-distance graph on R^n, for n >= 3.

  The reasoning behind the verification procedure is explained in file
  "verify.tex", found together with the arXiv version of the original
  paper. Files containing solution data are also to be found together
  with the arXiv version of the paper; they are:

    FILE       INFO
    rn3.dat    Bound for R^3
    rn4.dat    Bound for R^4
    rn5.dat    Bound for R^5
    rn6.dat    Bound for R^6
    rn7.dat    Bound for R^7
    rn8.dat    Bound for R^8

  To build this program you should run make from the command line. You
  need to have both MPFR and GMP installed.


  EXAMPLE USAGE:

  Call the program from the command line with the name of the file you
  want to use:

  > ./rn_verify rn3.dat


  INPUT FILE FORMAT:

  Here is a description of the input file format for the verification
  procedure.

  The first line contains 4 space-separated numbers. The first one is
  the dimension n of the space. The second is the number L used for
  the verification. The next two numbers, a and b, are lower and upper
  bounds on the rightmost root of the derivative of Omega_n in the
  interval [0, Lw], where w is defined as in the documentation file
  "verify.tex".

  The second line contains three space-separated numbers, the values
  of variables lambda, z2, and z3.

  Each of the following lines contains one of the constraints. The
  first number on the line is the value of the corresponding dual
  variable. Then comes a string, either "BQP", indicating a BQP
  constraint, or "SUBGRAPH", indicating a subgraph constraint.

  For a BQP constraint, the first number after "BQP" is always N, the
  dimension of the BQP constraint. Then comes the right-hand side and
  all diagonal and upper-diagonal entries of the constraint matrix
  (these should all be integers). For instance, the constraint <A, X>
  >= -1 with

          [ 1, 2, 3 ]
      A = [ 2, 4, 5 ]
          [ 3, 5, 6 ]

  is represented by the string "3 -1 1 2 3 4 5 6". After this, we have
  n * N numbers, which give the coordinates of the points
  corresponding to each row and column of the matrix.

  For a subgraph constraint, the first number after "SUBGRAPH" is the
  number of vertices of the graph. Then comes the independence number,
  followed by N, the dimension of the points used as coordinates of
  the vertices (we must have N <= n). Then comes N * V numbers, where
  V is the number of vertices, giving the coordinates of each vertex
  of the graph.

  Empty lines in the input file are ignored.
*/

#include <cmath>
#include <vector>
#include <fstream>
#include <sstream>
#include <cstring>
#include <iostream>
#include <mpfr.h>
#include "omega.h"

using namespace std;


// A linear constraint.
struct LinearConstraint {
    // Dual variable.
    double y;

    // Pairs (s, c), where s >= 0 and c = l(s).
    vector<pair<double, double>> lhs;

    // Right-hand side.
    double rhs;
};


// A dual solution.
struct EuclideanDualSolution {
    int n;

    // Endpoint of interval to be checked by sampling.
    double L;

    // Lower and upper bounds on zero of Bessel function.
    double ru, rl;

    // Dual variables.
    double lambda;
    double z2, z3;

    // Constraints.
    vector<LinearConstraint> constraints;
};


//
// Prototypes
//
double euclidean_distance(int n, const vector<double>& v,
                          int i, int j);
LinearConstraint parse_bqp_constraint(int n, double y, istream& in);
LinearConstraint parse_subgraph_constraint(int n, double y,
                                           istream& in);
EuclideanDualSolution read_dual_solution(istream& in);
void verify_limit_feasibility(const EuclideanDualSolution& g);
void estimate_bound(const EuclideanDualSolution& g);

//
// main
//
int main(int argc, char **argv)
{
    mpfr_set_default_prec(128);

    if (argc != 2) {
        cerr << "Usage: ";
        cerr << " rn_verify <solution-file>" << endl;
        return -1;
    }

    errno = 0;
    ifstream in{argv[1]};

    if (!in) {
        cerr << string("rn_verify: failed to open file '") + argv[1]
             << string("': ") + strerror(errno) << endl;
        exit(-1);
    }

    try {
        auto g = read_dual_solution(in);
        
        if (g.n < 3)
            throw runtime_error{"dimension must be >= 3"};
        
        verify_limit_feasibility(g);
        estimate_bound(g);
    }
    catch (runtime_error& e) {
        cerr << string("sn_verify: ") + argv[1] + ": " + e.what()
             << endl;
        return -1;
    }        
    
    return 0;
}


/*
  Return distance between two vectors.

  INPUT:

  n -- dimension of the vectors.

  v -- this array contains the concatenation of any number, say N, of
       vecotrs in R^n.

  i, j -- positions in v of the two vectors whose distance one wishes
          to compute. If v has N concatenated vectors, then we must
          have 0 <= i, j < N.
*/
double euclidean_distance(int n, const vector<double>& v,
                          int i, int j)
{
    double ret = 0;
    for (int k = 0; k < n; k++) {
        const double diff = v[i * n + k] - v[j * n + k];
        ret += diff * diff;
    }

    return sqrt(ret);
}


// Return linear BQP constraint read from stream.
LinearConstraint parse_bqp_constraint(int n, double y, istream& in)
{
    LinearConstraint C;

    C.y = y;
    
    int N;
        
    if (!(in >> N) || !(in >> C.rhs))
        throw runtime_error{"invalid BQP constraint"};

    if (N <= 1)
        throw runtime_error{"invalid size of BQP constraint"};

    // Read the BQP constraint matrix.
    vector<vector<int>> B;

    for (int i = 0; i < N; i++)
        B.emplace_back(N);

    for (int i = 0; i < N; i++)
        for (int j = i; j < N; j++) {
            if (!(in >> B[i][j]))
                throw runtime_error{"too few numbers for"
                        " BQP constraint"};
            
            B[j][i] = B[i][j];
        }
    
    // Read the supporting points.
    vector<double> x;
    double val;
    while (in >> val)
        x.push_back(val);

    if (x.size() != n * N)
        throw runtime_error{"wrong number of values"
                " for supporting points"};

    // TODO: explain.
    double l0 = 0;  // Sum of all l(0) values from the diagonal entries.

    for (int i = 0; i < N; i++) {
        l0 += B[i][i];
        
        for (int j = i + 1; j < N; j++)
            if (B[i][j] != 0) {
                const double dst = euclidean_distance(n, x, i, j);

                C.lhs.emplace_back(dst, 2 * B[i][j]);
            }
    }
    
    C.lhs.emplace_back(0, l0);

    return C;
}


// Return linear subgraph constraint read from stream.
LinearConstraint parse_subgraph_constraint(int n, double y,
                                           istream& in)
{
    LinearConstraint C;

    C.y = y;

    int nverts, alpha, dim;
            
    if (!(in >> nverts) || !(in >> alpha) || !(in >> dim)
        || nverts <= 0 || alpha <= 0 || alpha > nverts
        || dim > n || dim <= 1)
        throw runtime_error{"invalid subgraph constraint"};
    
    // Read the supporting points.
    vector<double> x;
    double val;
    while (in >> val)
        x.push_back(val);

    if (x.size() != dim * nverts)
        throw runtime_error{"wrong number of values"
                " for supporting points"};

    C.lhs.emplace_back(0, alpha);

    for (int i = 0; i < nverts; i++) {
        double norm_sq = 0;
        
        for (int k = 0; k < dim; k++)
            norm_sq += x[i * dim + k] * x[i * dim + k];
        
        C.lhs.emplace_back(sqrt(norm_sq), -1);
    }

    return C;
}


// Return dual solution read from stream.
EuclideanDualSolution read_dual_solution(istream& in)
{
    EuclideanDualSolution g;

    // Read n and magic numbers.
    {
        string s;
        
        if (!getline(in, s))
            throw runtime_error{"1: failed to read dimension and"
                    " magic numbers"};

        istringstream iss{s};

        if (!(iss >> g.n) || g.n <= 1)
            throw runtime_error{"1: invalid dimension"};

        if (!(iss >> g.L) || !(iss >> g.rl) || !(iss >> g.ru))
            throw runtime_error{"1: failed to read magic numbers"};
    }

    // Testing the magic numbers.
    if (g.L <= 10)
        throw runtime_error{"1: invalid L value"};

    if (g.rl > g.ru)
        throw runtime_error{"1: invalid bounds on zero of"
                " Bessel function"};

    mpfr_t val_l, val_u, x;
    mpfr_inits(val_l, val_u, x, nullptr);

    if (g.n % 2 == 0) {
        IntegerBesselJ bessel(g.n / 2);

        mpfr_set_d(x, g.rl, MPFR_RNDN);
        bessel.eval(val_l, x);

        mpfr_set_d(x, g.ru, MPFR_RNDN);
        bessel.eval(val_u, x);
    }
    else {
        HalfIntegerBesselJ bessel(g.n / 2);

        mpfr_set_d(x, g.rl, MPFR_RNDN);
        bessel.eval(val_l, x);

        mpfr_set_d(x, g.ru, MPFR_RNDN);
        bessel.eval(val_u, x);
    }

    {
        int a = mpfr_cmp_si(val_l, 0);
        int b = mpfr_cmp_si(val_u, 0);

        if ((a >= 0 && b >= 0) || (a <= 0 && b <= 0))
            throw runtime_error{"invalid bounds on zero of"
                    " Bessel function"};
    }

    mpfr_clears(val_l, val_u, x, nullptr);
    
    // Read lambda, z2, and z3.
    {
        string s;

        if (!getline(in, s))
            throw runtime_error{"2: failed to read lambda, z2, and z3"};

        istringstream iss{s};

        if (!(iss >> g.lambda) || !(iss >> g.z2) || !(iss >> g.z3)
            || g.lambda <= 0 || g.z3 > 0)
            throw runtime_error{"2: invalid lambda, z2, or z3"};
    }

    // Read each linear constraint.
    string s;
    for (int lineno = 3; getline(in, s); lineno++) {
        double y;
        string tmp;
        istringstream iss{s};

        if (!(iss >> y) || !(iss >> tmp)) continue;

        if (y > 0)
            throw runtime_error{to_string(lineno)
                    + ": invalid dual variable value"};

        try {
            if (tmp == "BQP")
                g.constraints.push_back(
                    parse_bqp_constraint(g.n, y, iss)
                );
            else if (tmp == "SUBGRAPH")
                g.constraints.push_back(
                    parse_subgraph_constraint(g.n, y, iss)
                );
            else
                throw runtime_error{"unkown constraint type"};
        }
        catch (runtime_error& e) {
            throw runtime_error{to_string(lineno) + ": " + e.what()};
        }
    }
    
    return g;    
}


// Verify that the dual solution if feasible at infinity, that is,
// that the function is positive at infinity, and check that it is
// sufficient to find the minimum on the interval [0, g.L], given the
// estimates g.rl and g.ru on a zero of the derivative of
// Omega_n. This function throws runtime_error if there is a problem.
void verify_limit_feasibility(const EuclideanDualSolution& g)
{
    mpfr_t acc, viol, omega_bound, x;

    mpfr_inits(acc, viol, omega_bound, x, nullptr);

    // Compute limit violation.
    mpfr_set_si(viol, -1, MPFR_RNDN);
    mpfr_add_d(viol, viol, g.z2, MPFR_RNDN);

    for (auto& C : g.constraints)
        for (auto& p : C.lhs)
            if (p.first == 0)
                mpfr_add_d(viol, viol, C.y * p.second, MPFR_RNDN);

    if (mpfr_cmp_ui(viol, 0) <= 0)
        throw runtime_error{"solution infeasible at infinity"};

    // Then check if the interval for verification is correct.
    double w = 1;  // Nonzero distance closest to zero.

    for (auto& C : g.constraints)
        for (auto& p : C.lhs)
            if (p.first > 0 && p.first < w)
                w = p.first;

    // Check if the Bessel function's zero is ok and compute bound on
    // the derivative.
    OmegaFunc omega{g.n};

    if (w * g.L < g.ru)
        throw runtime_error{"invalid zero for Bessel function"};
    
    mpfr_set_d(x, g.ru, MPFR_RNDN);
    omega.eval(omega_bound, x);
    mpfr_abs(omega_bound, omega_bound, MPFR_RNDN);
    mpfr_add_d(omega_bound, omega_bound, fabs(g.ru - g.rl),
               MPFR_RNDN);

    mpfr_set_d(acc, -fabs(g.lambda), MPFR_RNDN);
    mpfr_mul(acc, acc, omega_bound, MPFR_RNDN);

    for (auto& C : g.constraints)
        for (auto& p : C.lhs)
            if (p.first > 0) {
                mpfr_set_d(x, C.y, MPFR_RNDN);
                mpfr_mul_d(x, x, fabs(p.second), MPFR_RNDN);
                mpfr_mul(x, x, omega_bound, MPFR_RNDN);
                mpfr_add(acc, acc, x, MPFR_RNDN);
            }

    // Final test.
    mpfr_mul_d(viol, viol, 0.99, MPFR_RNDN);
    mpfr_add(acc, acc, viol, MPFR_RNDN);

    if (mpfr_cmp_si(acc, 0) < 0)
        throw runtime_error{"invalid estimate for L parameter"};    
}


// Estimate a correct upper bound by computing a bound on the maximum
// dual violation in [0, g.L].
void estimate_bound(const EuclideanDualSolution& g)
{
    // Intermediary variables.
    mpfr_t x, y, z;

    mpfr_inits(x, y, z, nullptr);
    
    // Determine s and bound on derivative on interval [0, s].
    mpfr_set_d(x, g.n / 2.0, MPFR_RNDN);
    mpfr_gamma(x, x, MPFR_RNDN);

    const double s = pow(g.n * mpfr_get_d(x, MPFR_RNDN)
                         * pow(2, (g.n - 3) / 2.0), 2.0 / g.n);

    // eta is the additive error we are aiming at for the minimum. To
    // give a nice progress report, we compute how many points are
    // going to be evaluated, but we do so using at first double
    // arithmetic only.
    const double eta = 1e-4;

    mpfr_set_d(x, g.n / 2.0, MPFR_RNDN);
    mpfr_gamma(x, x, MPFR_RNDN);
    const double gamma_fac = mpfr_get_d(x, MPFR_RNDN);
    
    unsigned long total_points = 0;
    for (double t = 0; t < g.L; t += 0.5) {
        double derivative_bound;

        if (t <= s)
            derivative_bound = fabs(g.lambda) * (s / g.n);
        else
            derivative_bound = fabs(g.lambda) * gamma_fac
                * pow(2 / t, (g.n - 2) / 2.0) / sqrt(2);

        for (auto& C : g.constraints)
            for (auto& p : C.lhs) {
                if (p.first == 0) continue;

                if (p.first * t <= s)
                    derivative_bound += fabs(C.y) * p.first
                        * fabs(p.second) * (s / g.n);
                else
                    derivative_bound += fabs(C.y) * p.first
                        * fabs(p.second) * gamma_fac
                        * pow(2 / (p.first * t), (g.n - 2) / 2.0)
                        / sqrt(2);
            }

        const double eps = eta / derivative_bound;
        total_points += ceil(0.5 / eps);
    }

    // Then we compute the minimum of the function up to an additive
    // error of eta.
    OmegaFunc omega{g.n};
    mpfr_t acc, eps, min;

    mpfr_inits(acc, eps, min, nullptr);
    mpfr_set_d(min, 100, MPFR_RNDN);

    cout << std::fixed;
    cout.precision(1);
    
    unsigned long cur_point = 0;
    for (double t = 0; t < g.L; t += 0.5) {
        // Compute upper bound on the derivative in [t, t + 0.5].
        double derivative_bound;

        if (t <= s)
            derivative_bound = fabs(g.lambda) * (s / g.n);
        else
            derivative_bound = fabs(g.lambda) * gamma_fac
                * pow(2 / t, (g.n - 2) / 2.0) / sqrt(2);
        
        for (auto& C : g.constraints)
            for (auto& p : C.lhs) {
                if (p.first == 0) continue;
                
                if (p.first * t <= s)
                    derivative_bound += fabs(C.y) * p.first
                        * fabs(p.second) * (s / g.n);
                else
                    derivative_bound += fabs(C.y) * p.first
                        * fabs(p.second) * gamma_fac
                        * pow(2 / (p.first * t), (g.n - 2) / 2.0)
                        / sqrt(2);
            }

        // Compute eps and perform checking.
        mpfr_set_d(x, derivative_bound, MPFR_RNDN);
        mpfr_d_div(eps, eta, x, MPFR_RNDN);
        mpfr_set_d(x, t, MPFR_RNDN);

        for ( ; mpfr_cmp_d(x, t + 0.5) < 0; cur_point++) {
            // Show progress.
            if (total_points < 1000
                || cur_point % (total_points / 1000) == 0) {
                cout << "\rEstimating minimum  "
                     << 100.0 * cur_point / total_points << "%  ";
                cout.flush();
            }
            
            // Compute function.
            omega.eval(acc, x);
            mpfr_mul_d(acc, acc, g.lambda, MPFR_RNDN);
            mpfr_add_d(acc, acc, g.z2 - 1, MPFR_RNDN);

            if (mpfr_zero_p(x))
                mpfr_add_d(acc, acc, g.z3, MPFR_RNDN);

            for (auto& C : g.constraints)
                for (auto& p : C.lhs) {
                    mpfr_mul_d(y, x, p.first, MPFR_RNDN);
                    omega.eval(z, y);
                    mpfr_mul_d(z, z, C.y * p.second, MPFR_RNDN);
                    mpfr_add(acc, acc, z, MPFR_RNDN);
                }

            if (mpfr_cmp(acc, min) < 0)
                mpfr_set(min, acc, MPFR_RNDN);
            
            mpfr_add(x, x, eps, MPFR_RNDN);
        }
    }

    cout << "\rEstimating minimum  100%  " << endl;
    
    // Compute z1.
    mpfr_sub_d(min, min, eta, MPFR_RNDN);
    
    if (mpfr_sgn(min) < 0) {
        // Make sure z3 is negative.
        mpfr_add_d(x, min, g.z3, MPFR_RNDN);

        // z2.
        mpfr_mul_si(y, min, -2, MPFR_RNDN);
        mpfr_add_d(y, y, g.z2, MPFR_RNDN);
    }
    else {
        mpfr_set_d(x, g.z3, MPFR_RNDN);
        mpfr_set_d(y, g.z2, MPFR_RNDN);
    }
    
    // z1.
    mpfr_mul(z, y, y, MPFR_RNDN);
    mpfr_mul_si(z, z, -1, MPFR_RNDN);
    mpfr_div_ui(z, z, 4, MPFR_RNDN);
    mpfr_div(z, z, x, MPFR_RNDN);
            
    // Compute upper bound.
    mpfr_set(acc, z, MPFR_RNDN);

    for (auto& C : g.constraints)
        mpfr_add_d(acc, acc, C.y * C.rhs, MPFR_RNDN);

    mpfr_printf("Solution checked; minimum = %.15Rf; bound = %.15Rf\n",
                min, acc);
}

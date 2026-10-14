Verification program and dual solution for m1(R^3) <= 0.1533 by DeCorte, Oliveira and Vallentin, from the arXiv
ancillary files of arXiv:1804.09099. One portability fix: the base-class destructor `~BesselJ()` in `omega.h` was
made virtual (modern clang traps on deleting through a non-virtual base). The arithmetic is unchanged.

Build: `make CXX="c++ -I/opt/homebrew/include -L/opt/homebrew/lib" rn_verify`, then `./rn_verify rn3.dat`.
Output, in `verify_run.log`: "Solution checked; minimum = -0.000101042537327; bound = 0.153299568560593".

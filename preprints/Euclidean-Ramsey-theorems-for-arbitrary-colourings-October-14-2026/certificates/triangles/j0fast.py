"""ctypes wrapper for libj0fast: j0(x_array), j0sum(r, c, t). ERR = rigorous abs error bound per J0 value."""
import ctypes, os, numpy as np
_lib = ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'libj0fast.dylib'))
_D = ctypes.POINTER(ctypes.c_double)
_lib.j0v.argtypes = [_D, _D, ctypes.c_long]
_lib.j0sum.argtypes = [_D, _D, ctypes.c_int, _D, _D, ctypes.c_long]
ERR = 1e-14
def j0(x):
    x = np.ascontiguousarray(x, dtype=np.float64); y = np.empty_like(x)
    _lib.j0v(x.ctypes.data_as(_D), y.ctypes.data_as(_D), x.size); return y
def j0sum(r, c, t):
    r = np.ascontiguousarray(r, dtype=np.float64); c = np.ascontiguousarray(c, dtype=np.float64)
    t = np.ascontiguousarray(t, dtype=np.float64); out = np.empty_like(t)
    _lib.j0sum(r.ctypes.data_as(_D), c.ctypes.data_as(_D), len(r), t.ctypes.data_as(_D), out.ctypes.data_as(_D), t.size)
    return out
_lib.j0sum_mt.argtypes = [_D, _D, ctypes.c_int, _D, _D, ctypes.c_long, ctypes.c_int]
def j0sum_mt(r, c, t, nthreads=3):
    r = np.ascontiguousarray(r, dtype=np.float64); c = np.ascontiguousarray(c, dtype=np.float64)
    t = np.ascontiguousarray(t, dtype=np.float64); out = np.empty_like(t)
    _lib.j0sum_mt(r.ctypes.data_as(_D), c.ctypes.data_as(_D), len(r), t.ctypes.data_as(_D), out.ctypes.data_as(_D), t.size, nthreads)
    return out

# Checks that every edge of edge2278_graph.json is a unit distance between the 509 points of
# parts509_coordinates.vtx (the 509-vertex graph of Parts, 2442 unit edges), at 60-digit precision,
# and that the edges are a subset of the 2442 unit pairs.  Usage: python3 check_unit.py parts509_coordinates.vtx edge2278_graph.json
import json, sys, mpmath as mp
mp.mp.dps = 60
pts = []
for line in open(sys.argv[1]):
    line = line.strip()
    if not line: continue
    import re; line = re.sub(r'(?<![\w.])(\d+)', r"mp.mpf('\1')", line)
    e = line.replace('Sqrt', 'mp.sqrt').replace('{', '(').replace('}', ')').replace('[', '(').replace(']', ')')
    pts.append(tuple(mp.mpf(1)*c for c in eval(e)))
G = json.load(open(sys.argv[2])); E = G['edges']
print("points", len(pts), "edges", len(E))
worst = max(abs((pts[i][0]-pts[j][0])**2 + (pts[i][1]-pts[j][1])**2 - 1) for i, j in E)
print("max |d^2 - 1| over edges:", mp.nstr(worst, 5))
unit = set()
n = len(pts)
for i in range(n):
    for j in range(i+1, n):
        d = (pts[i][0]-pts[j][0])**2 + (pts[i][1]-pts[j][1])**2 - 1
        if abs(d) < mp.mpf(10)**-40: unit.add((i, j))
        elif abs(d) < mp.mpf(10)**-10: print("SUSPICIOUS near-unit pair", i, j, mp.nstr(d, 5))
print("unit pairs among the 509 points (|d^2-1| < 1e-40):", len(unit))
print("all 2278 edges among them:", all(tuple(sorted(e)) in unit for e in E))

import json, sys
from fractions import Fraction as F
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
d = json.load(open(sys.argv[1])); B = [[float(F(x)) for x in r] for r in d['B']]
cols = ['#d1495b', '#edae49', '#00798c', '#30638e', '#e8e3d9']
fig, ax = plt.subplots(figsize=(7, 7))
for P, c in zip(d['polys'], d['cols']):
    P = [(float(F(x)), float(F(y))) for x, y in P]
    for m in range(-2, 3):
        for n in range(-2, 3):
            t = (m*B[0][0] + n*B[1][0], m*B[0][1] + n*B[1][1])
            ax.add_patch(Polygon([(x+t[0], y+t[1]) for x, y in P], fc=cols[c], ec=cols[c], lw=0.4))
ax.plot([0.2, 1.2], [0.3, 0.3], color='k', lw=3, solid_capstyle='butt', zorder=10); ax.text(0.7, 0.42, '1', ha='center', va='bottom', fontsize=13, zorder=10, bbox=dict(fc='white', ec='none', pad=1))
ax.set_xlim(-3, 9); ax.set_ylim(-3, 9); ax.set_aspect('equal'); ax.axis('off')
plt.savefig(sys.argv[2], dpi=160, bbox_inches='tight')
import collections
area = collections.Counter()
for P, c in zip(d['polys'], d['cols']):
    P = [(F(x), F(y)) for x, y in P]; n = len(P)
    area[c] += abs(sum(P[i][0]*P[(i+1)%n][1]-P[(i+1)%n][0]*P[i][1] for i in range(n))/2)
tot = sum(area.values()); print({c: round(float(a/tot), 4) for c, a in sorted(area.items())})

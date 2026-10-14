"""Exact rational certificate for a positive-margin asymmetric tiling.

The independent parameters in ``asym_safe.npy`` are rounded to six decimal
places and then treated as rational numbers.  All checks below use Fraction:

* every polygon is simple;
* periodic tile interiors do not overlap and their exact total area equals
  the lattice-cell area (hence the closed tiles cover the plane);
* each of the five unit-avoiding tile types has diameter < 1 and distinct
  periodic copies are more than 1 apart;
* the union of the three red tile types has component diameter below the
  requested rational distance and distinct components are farther apart.

Choosing any deterministic owner for shared boundary points therefore gives
a coloring of type (1,1,1,1,1,133/200).
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
RADIUS = 6

Point = tuple[F, F]
Polygon = tuple[Point, ...]


def add(a: Point, b: Point) -> Point:
    return a[0] + b[0], a[1] + b[1]


def sub(a: Point, b: Point) -> Point:
    return a[0] - b[0], a[1] - b[1]


def scale(k: F, a: Point) -> Point:
    return k * a[0], k * a[1]


def dot(a: Point, b: Point) -> F:
    return a[0] * b[0] + a[1] * b[1]


def cross(a: Point, b: Point) -> F:
    return a[0] * b[1] - a[1] * b[0]


def squared_distance(a: Point, b: Point) -> F:
    delta = sub(a, b)
    return dot(delta, delta)


def translate(polygon: Polygon, offset: Point) -> Polygon:
    return tuple(add(point, offset) for point in polygon)


def signed_double_area(polygon: Polygon) -> F:
    return sum(
        cross(polygon[i], polygon[(i + 1) % len(polygon)])
        for i in range(len(polygon))
    )


def orientation(a: Point, b: Point, c: Point) -> F:
    return cross(sub(b, a), sub(c, a))


def on_segment(point: Point, a: Point, b: Point) -> bool:
    return (
        orientation(a, b, point) == 0
        and min(a[0], b[0]) <= point[0] <= max(a[0], b[0])
        and min(a[1], b[1]) <= point[1] <= max(a[1], b[1])
    )


def segments_intersect(a: Point, b: Point, c: Point, d: Point) -> bool:
    o1, o2 = orientation(a, b, c), orientation(a, b, d)
    o3, o4 = orientation(c, d, a), orientation(c, d, b)
    if (o1 > 0 > o2 or o2 > 0 > o1) and (o3 > 0 > o4 or o4 > 0 > o3):
        return True
    return (
        (o1 == 0 and on_segment(c, a, b))
        or (o2 == 0 and on_segment(d, a, b))
        or (o3 == 0 and on_segment(a, c, d))
        or (o4 == 0 and on_segment(b, c, d))
    )


def proper_segments_intersect(a: Point, b: Point, c: Point, d: Point) -> bool:
    o1, o2 = orientation(a, b, c), orientation(a, b, d)
    o3, o4 = orientation(c, d, a), orientation(c, d, b)
    return (o1 > 0 > o2 or o2 > 0 > o1) and (
        o3 > 0 > o4 or o4 > 0 > o3
    )


def point_strictly_inside(point: Point, polygon: Polygon) -> bool:
    for i in range(len(polygon)):
        if on_segment(point, polygon[i], polygon[(i + 1) % len(polygon)]):
            return False
    inside = False
    x, y = point
    for i in range(len(polygon)):
        x1, y1 = polygon[i]
        x2, y2 = polygon[(i + 1) % len(polygon)]
        if (y1 > y) != (y2 > y):
            intersection_x = x1 + (y - y1) * (x2 - x1) / (y2 - y1)
            if intersection_x > x:
                inside = not inside
    return inside


def point_on_boundary(point: Point, polygon: Polygon) -> bool:
    return any(
        on_segment(point, polygon[i], polygon[(i + 1) % len(polygon)])
        for i in range(len(polygon))
    )


def polygon_is_simple(polygon: Polygon) -> bool:
    n = len(polygon)
    if len(set(polygon)) != n or signed_double_area(polygon) == 0:
        return False
    for i in range(n):
        a, b = polygon[i], polygon[(i + 1) % n]
        for j in range(i + 1, n):
            if (j - i) in (0, 1, n - 1):
                continue
            c, d = polygon[j], polygon[(j + 1) % n]
            if segments_intersect(a, b, c, d):
                return False
    return True


def polygon_interiors_overlap(left: Polygon, right: Polygon) -> bool:
    for i in range(len(left)):
        a, b = left[i], left[(i + 1) % len(left)]
        for j in range(len(right)):
            c, d = right[j], right[(j + 1) % len(right)]
            if proper_segments_intersect(a, b, c, d):
                return True
    if any(point_strictly_inside(point, right) for point in left):
        return True
    if any(point_strictly_inside(point, left) for point in right):
        return True
    # This catches coincident-region degeneracies and cases in which the only
    # available strict interior witness lies between listed vertices.
    left_midpoints = [
        scale(F(1, 2), add(left[i], left[(i + 1) % len(left)]))
        for i in range(len(left))
    ]
    right_midpoints = [
        scale(F(1, 2), add(right[i], right[(i + 1) % len(right)]))
        for i in range(len(right))
    ]
    if any(point_strictly_inside(point, right) for point in left_midpoints):
        return True
    if any(point_strictly_inside(point, left) for point in right_midpoints):
        return True
    if all(point_on_boundary(point, right) for point in left) and all(
        point_on_boundary(point, left) for point in right
    ):
        return True
    return False


def point_segment_squared_distance(point: Point, a: Point, b: Point) -> F:
    edge = sub(b, a)
    edge_squared = dot(edge, edge)
    projection = dot(sub(point, a), edge)
    if projection <= 0:
        return squared_distance(point, a)
    if projection >= edge_squared:
        return squared_distance(point, b)
    return cross(edge, sub(point, a)) ** 2 / edge_squared


def segment_squared_distance(a: Point, b: Point, c: Point, d: Point) -> F:
    if segments_intersect(a, b, c, d):
        return F(0)
    return min(
        point_segment_squared_distance(a, c, d),
        point_segment_squared_distance(b, c, d),
        point_segment_squared_distance(c, a, b),
        point_segment_squared_distance(d, a, b),
    )


def polygon_squared_distance(left: Polygon, right: Polygon) -> F:
    return min(
        segment_squared_distance(
            left[i],
            left[(i + 1) % len(left)],
            right[j],
            right[(j + 1) % len(right)],
        )
        for i in range(len(left))
        for j in range(len(right))
    )


def rational_parameter(value: float, digits: int) -> F:
    return F(f"{value:.{digits}f}")


def build_rational(parameters: list[F]) -> tuple[dict[str, Polygon], F, F]:
    names = [
        "B",
        "PA",
        "PB",
        "X",
        "MAA",
        "XX",
        "XXX",
        "I1",
        "I2",
        "I3",
        "I4",
        "M",
        "N",
        "MM",
        "NN",
    ]
    points = {
        name: (parameters[2 * i], parameters[2 * i + 1])
        for i, name in enumerate(names)
    }
    p, h = parameters[30], parameters[31]
    lattice_1 = (p, F(0))
    lattice_2 = (p / 2, h)
    zero = (F(0), F(0))
    a = zero
    b, pa, pb = points["B"], points["PA"], points["PB"]
    x, maa, xx, xxx = (
        points["X"],
        points["MAA"],
        points["XX"],
        points["XXX"],
    )
    i1, i2, i3, i4 = (
        points["I1"],
        points["I2"],
        points["I3"],
        points["I4"],
    )
    m, n, mm, nn = points["M"], points["N"], points["MM"], points["NN"]
    c = add(a, lattice_2)
    aa = sub(add(b, lattice_1), lattice_2)
    pd = add(pb, lattice_2)
    pc = add(pb, lattice_1)
    i5 = add(i1, lattice_2)
    i6 = sub(add(i4, lattice_2), lattice_1)
    y = sub(add(maa, lattice_2), lattice_1)
    z = add(maa, lattice_2)
    yy = sub(add(xxx, lattice_2), lattice_1)
    zz = add(xx, lattice_2)
    mmm = sub(mm, lattice_2)
    nnn = sub(add(nn, lattice_1), lattice_2)
    shift = sub(lattice_1, lattice_2)

    def shifted(values: list[Point], offset: Point) -> Polygon:
        return tuple(add(value, offset) for value in values)

    tiles = {
        "red_P1": tuple([pa, i2, m, n, i3]),
        "red_P2": tuple([i5, mm, nn, i6, pd]),
        "red_Q": tuple([x, xx, maa, xxx]),
        "turq": tuple([x, xx, a, mmm, i1, i2, pa]),
        "yell": tuple([x, xxx, aa, nnn, i4, i3, pa]),
        "green": shifted([y, yy, b, m, i2, i1, pb], shift),
        "oran": shifted([z, zz, c, n, i3, i4, pc], scale(F(-1), lattice_2)),
        "blue": shifted([m, n, c, mm, nn, b], shift),
    }
    return tiles, p, h


def lattice_offset(i: int, j: int, p: F, h: F) -> Point:
    return F(i) * p + F(j) * p / 2, F(j) * h


def ordered_periodic_pairs(keys: list[str]):
    for left_index, left in enumerate(keys):
        for right_index in range(left_index, len(keys)):
            right = keys[right_index]
            for i, j in product(range(-RADIUS, RADIUS + 1), repeat=2):
                if left_index == right_index and (i, j) <= (0, 0):
                    continue
                yield left, right, i, j


def outer_range_is_safe(tiles: dict[str, Polygon], p: F, h: F) -> None:
    all_points = [point for polygon in tiles.values() for point in polygon]
    x_span = max(point[0] for point in all_points) - min(
        point[0] for point in all_points
    )
    y_span = max(point[1] for point in all_points) - min(
        point[1] for point in all_points
    )
    if (RADIUS + 1) * h <= y_span:
        raise AssertionError("translation radius does not dominate vertical span")
    minimum_far_x = p * (F(RADIUS + 1) - F(RADIUS, 2))
    if minimum_far_x <= x_span:
        raise AssertionError("translation radius does not dominate horizontal span")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=HERE / "asym_safe.npy")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--digits", type=int, default=6)
    args = parser.parse_args()

    floating = np.load(args.input)
    distance = rational_parameter(float(floating[-1]), args.digits)
    parameters = [
        rational_parameter(float(value), args.digits) for value in floating[:-1]
    ]
    tiles, p, h = build_rational(parameters)
    outer_range_is_safe(tiles, p, h)

    for name, polygon in tiles.items():
        if not polygon_is_simple(polygon):
            raise AssertionError(f"{name} is not a simple rational polygon")

    # Exact periodic non-overlap.  Touching and shared boundary segments are
    # allowed; proper crossings and strict containment are not.
    tile_keys = list(tiles)
    for left, right, i, j in ordered_periodic_pairs(tile_keys):
        moved = translate(tiles[right], lattice_offset(i, j, p, h))
        if polygon_interiors_overlap(tiles[left], moved):
            raise AssertionError(f"interior overlap: {left}, {right}, shift {(i, j)}")

    total_double_area = sum(abs(signed_double_area(tile)) for tile in tiles.values())
    cell_double_area = 2 * p * h
    if total_double_area != cell_double_area:
        raise AssertionError(
            f"area mismatch: tiles={total_double_area}, cell={cell_double_area}"
        )

    unit_keys = ["turq", "yell", "green", "oran", "blue"]
    red_keys = ["red_P1", "red_P2", "red_Q"]
    diameter_slacks: list[F] = []
    separation_slacks: list[F] = []
    maximum_diameter_squared: dict[str, F] = {}
    minimum_separation_squared: dict[str, F] = {}

    for key in unit_keys + red_keys:
        threshold = F(1) if key in unit_keys else distance
        threshold_squared = threshold**2
        maximum_squared = max(
            squared_distance(a, b) for a, b in combinations(tiles[key], 2)
        )
        slack = threshold_squared - maximum_squared
        if slack <= 0:
            raise AssertionError(f"diameter failure for {key}: squared slack {slack}")
        diameter_slacks.append(slack)
        maximum_diameter_squared[key] = maximum_squared

    separation_families = [([key], F(1)) for key in unit_keys]
    separation_families.append((red_keys, distance))
    for keys, threshold in separation_families:
        for left, right, i, j in ordered_periodic_pairs(keys):
            moved = translate(tiles[right], lattice_offset(i, j, p, h))
            squared = polygon_squared_distance(tiles[left], moved)
            slack = squared - threshold**2
            if slack <= 0:
                raise AssertionError(
                    f"separation failure: {left}, {right}, shift {(i, j)}, "
                    f"squared slack {slack}"
                )
            separation_slacks.append(slack)
            family_name = keys[0] if len(keys) == 1 else "red"
            minimum_separation_squared[family_name] = min(
                minimum_separation_squared.get(family_name, squared), squared
            )

    red_maximum_diameter_squared = max(
        maximum_diameter_squared[key] for key in red_keys
    )
    red_minimum_separation_squared = minimum_separation_squared["red"]

    result = {
        "distance": str(distance),
        "rounded_decimal_places": args.digits,
        "parameters": [str(value) for value in parameters],
        "lattice": {"p": str(p), "h": str(h)},
        "tile_count": len(tiles),
        "translation_radius": RADIUS,
        "exact_area_identity": True,
        "minimum_squared_diameter_slack": str(min(diameter_slacks)),
        "minimum_squared_separation_slack": str(min(separation_slacks)),
        "minimum_squared_diameter_slack_decimal": float(min(diameter_slacks)),
        "minimum_squared_separation_slack_decimal": float(min(separation_slacks)),
        "red_maximum_component_diameter_squared": str(
            red_maximum_diameter_squared
        ),
        "red_minimum_component_separation_squared": str(
            red_minimum_separation_squared
        ),
        "red_avoided_distance_interval": (
            "(sqrt(red_maximum_component_diameter_squared), "
            "sqrt(red_minimum_component_separation_squared))"
        ),
        "conclusion": (
            "exact rational coloring of type "
            f"(1,1,1,1,1,{distance})"
        ),
    }
    output = args.output or args.input.with_name(
        args.input.stem.replace("asym_", "certificate_") + ".json"
    )
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"wrote {output}")


if __name__ == "__main__":
    main()

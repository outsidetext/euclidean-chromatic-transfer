"""Check that exact rational certificates cover a continuous d-interval."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path


def fraction(text: str) -> F:
    return F(text)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificates", nargs="*", type=Path)
    parser.add_argument("--left", default="657/1000")
    parser.add_argument("--right", default="667504532081/1000000000000")
    args = parser.parse_args()

    certificate_paths = args.certificates or sorted(
        Path(__file__).resolve().parent.glob("certificate_*.json")
    )
    records = [json.loads(path.read_text()) for path in certificate_paths]
    records.sort(key=lambda record: fraction(record["distance"]))
    intervals = [
        (
            fraction(record["red_maximum_component_diameter_squared"]),
            fraction(record["red_minimum_component_separation_squared"]),
            record["distance"],
        )
        for record in records
    ]

    left = fraction(args.left)
    right = fraction(args.right)
    if intervals[0][0] >= left**2:
        raise AssertionError("the first open interval does not contain the left endpoint")
    for previous, current in zip(intervals, intervals[1:]):
        if previous[1] <= current[0]:
            raise AssertionError(
                f"gap between certificates centered at {previous[2]} and {current[2]}"
            )
    if intervals[-1][1] <= right**2:
        raise AssertionError("the final open interval does not contain the right endpoint")

    print(
        f"CERTIFIED CONTINUOUS COVERAGE: every d in [{left}, {right}] "
        f"is avoided by the sixth color in one of {len(intervals)} exact tilings"
    )
    for lower_squared, upper_squared, center in intervals:
        print(
            f"  center {center}: squared interval "
            f"({lower_squared}, {upper_squared})"
        )


if __name__ == "__main__":
    main()

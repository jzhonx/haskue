#!/usr/bin/env python3

import argparse
import json
import math
import sys
from pathlib import Path


def non_negative_number(value: str) -> float:
    try:
        number = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("must be a number") from error
    if not math.isfinite(number) or number < 0:
        raise argparse.ArgumentTypeError("must be a non-negative finite number")
    return number


def load_times(path: Path) -> dict[str, float]:
    with path.open(encoding="utf-8") as report_file:
        report = json.load(report_file)

    try:
        benchmarks = report[2]
    except (IndexError, TypeError) as error:
        raise ValueError(f"{path}: invalid Criterion report") from error

    times = {}
    for benchmark in benchmarks:
        try:
            name = benchmark["reportName"]
            regressions = benchmark["reportAnalysis"]["anRegress"]
            seconds = next(
                regression["regCoeffs"]["iters"]["estPoint"]
                for regression in regressions
                if regression["regResponder"] == "time"
            )
        except (KeyError, StopIteration, TypeError) as error:
            raise ValueError(f"{path}: incomplete Criterion benchmark result") from error

        if name in times:
            raise ValueError(f"{path}: duplicate benchmark {name!r}")
        times[name] = float(seconds)

    return times


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare Criterion benchmark results with a checked-in baseline."
    )
    parser.add_argument("baseline", type=Path, help="checked-in Criterion JSON report")
    parser.add_argument("current", type=Path, help="new Criterion JSON report")
    parser.add_argument(
        "--tolerance-percent",
        type=non_negative_number,
        default=20.0,
        help="allowed difference from the baseline (default: 20)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        baseline_times = load_times(args.baseline)
        current_times = load_times(args.current)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(error, file=sys.stderr)
        return 2

    names = sorted(baseline_times.keys() | current_times.keys())
    passed = bool(names)

    for name in names:
        if name not in baseline_times:
            print(f"{name}: missing from the checked-in baseline")
            passed = False
            continue
        if name not in current_times:
            print(f"{name}: missing from the current benchmark results")
            passed = False
            continue

        baseline = baseline_times[name]
        current = current_times[name]
        fraction = args.tolerance_percent / 100
        minimum = baseline * (1 - fraction)
        maximum = baseline * (1 + fraction)
        benchmark_passed = minimum <= current <= maximum
        passed = passed and benchmark_passed

        print(
            f"{name}: {current:.6f}s "
            f"(baseline {baseline:.6f}s, allowed {minimum:.6f}s–{maximum:.6f}s)"
        )

    sys.stdout.flush()
    if passed:
        print("All benchmark durations are within the allowed range.")
        return 0

    print(
        "One or more benchmark durations are outside the allowed range.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())

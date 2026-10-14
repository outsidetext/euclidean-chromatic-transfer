"""Regenerate every exact tiling certificate, then verify interval coverage."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent


def main() -> None:
    certificate_paths = sorted(HERE.glob("certificate_*.json"))
    for index, certificate in enumerate(certificate_paths, 1):
        suffix = certificate.stem.removeprefix("certificate_")
        candidate = HERE / f"asym_{suffix}.npy"
        if not candidate.exists() and suffix == "665":
            candidate = HERE / "asym_safe.npy"
        if not candidate.exists():
            raise FileNotFoundError(f"no candidate array for {certificate.name}")
        metadata = json.loads(certificate.read_text())
        digits = int(metadata["rounded_decimal_places"])
        print(
            f"[{index}/{len(certificate_paths)}] exact-checking {certificate.name}",
            flush=True,
        )
        subprocess.run(
            [
                sys.executable,
                str(HERE / "rigorous_verify.py"),
                "--input",
                str(candidate),
                "--output",
                str(certificate),
                "--digits",
                str(digits),
            ],
            check=True,
            stdout=subprocess.DEVNULL,
        )

    subprocess.run([sys.executable, str(HERE / "verify_continuum.py")], check=True)


if __name__ == "__main__":
    main()

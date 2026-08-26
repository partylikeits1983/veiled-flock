#!/usr/bin/env python3
"""Concrete Flock knowledge-error ledger.

This script deliberately prints separate provable and conjectured columns.
The standalone F2^128 Fiat-Shamir profile is never labelled provable-100.
"""

import argparse
import json
import math
from pathlib import Path


def bits_of_ratio(numerator: int, denominator_bits: int) -> float:
    return denominator_bits - math.log2(numerator)


def ledger(q_log2: int) -> dict:
    # The L0 fold access structure is already enough to cap the theorem.
    # Additional positive terms can only reduce the final number.
    fold_numerator = 257
    interactive_bits_f128 = bits_of_ratio(fold_numerator, 128)
    fs_bits_f128 = interactive_bits_f128 - math.log2(2**q_log2 + 1)
    interactive_bits_f256 = bits_of_ratio(fold_numerator, 256)
    fs_bits_f256 = interactive_bits_f256 - math.log2(2**q_log2 + 1)
    return {
        "protocol": "flock-zk-fv",
        "adversary_random_oracle_queries_log2": q_log2,
        "dominant_interactive_term": "257/2^field_bits (L0 fold access structure)",
        "profiles": [
            {
                "name": "standalone-fs-f128",
                "interactive_lower_bound_bits": interactive_bits_f128,
                "provable_knowledge_bits": fs_bits_f128,
                "knowledge_label": "100-bit conjectured classical knowledge security",
                "provable_100": False,
            },
            {
                "name": "two-stage-beacon-f128",
                "interactive_lower_bound_bits": interactive_bits_f128,
                "provable_knowledge_bits": interactive_bits_f128,
                "knowledge_label": "provable 100-bit with unbiased post-commitment challenge",
                "provable_100": interactive_bits_f128 >= 100,
            },
            {
                "name": "standalone-fs-challenge-f256",
                "interactive_lower_bound_bits": interactive_bits_f256,
                "provable_knowledge_bits": fs_bits_f256,
                "knowledge_label": "engineering profile; challenge-extension machinery not implemented",
                "provable_100": fs_bits_f256 >= 100,
            },
        ],
        "fs_theorem": "(Q+1)*kappa_Gamma plus Merkle and domain terms",
        "disallowed_conclusion": "100-bit standalone theorem over F2^128 at Q=2^64",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-log2", type=int, default=64)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = ledger(args.q_log2)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.check is not None:
        if args.check.read_text() != rendered:
            raise SystemExit(f"stale knowledge ledger: {args.check}")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()

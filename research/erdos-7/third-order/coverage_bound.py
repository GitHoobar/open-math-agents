"""Compute the third-order coverage bound for an odd period by integer arithmetic."""

import argparse
from math import prod


def prime_powers(period):
    rest = period
    candidate = 3
    while candidate * candidate <= rest:
        power = 1
        while rest % candidate == 0:
            power *= candidate
            rest //= candidate
        if power > 1:
            yield candidate, power
        candidate += 2
    if rest > 1:
        yield rest, rest


def third_order_bound(period):
    """Return the integer L*(A1 - A2 + A3), before capping it at L."""
    if period < 1 or period % 2 == 0:
        raise ValueError("the period must be a positive odd integer")
    factors = list(prime_powers(period))

    def scaled_product(t):
        return prod(power + t * ((power - 1) // (prime - 1))
                    for prime, power in factors)

    numerator = scaled_product(3) - 6 * scaled_product(2) + 15 * scaled_product(1) - 10 * period
    result, remainder = divmod(numerator, 6)
    if remainder:
        raise ArithmeticError("the unordered coprime-family sum must be an integer")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("period", type=int)
    args = parser.parse_args()
    try:
        upper = min(args.period, third_order_bound(args.period))
    except ValueError as exc:
        parser.error(str(exc))
    print(f"At most {upper} of {args.period} residues can be covered.")
    print(f"At least {args.period - upper} residues must remain uncovered.")

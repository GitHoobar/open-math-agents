"""Decide finite repair by moduli p**j * d for a fixed period and fresh prime."""

import argparse
from collections import deque
from math import gcd, isqrt


def divisors(n):
    small = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return small + [n // d for d in reversed(small) if d * d != n]


def smallest_fresh_prime(period):
    if period < 1 or period % 2 == 0:
        raise ValueError("the period must be positive and odd")
    candidate = 3
    while gcd(candidate, period) != 1:
        candidate += 2
    # A proper prime divisor of a composite candidate would qualify earlier.
    return candidate


def remove_class(state, divisor):
    """Yield outcomes of omitting this label or using it in one live child."""
    yield state
    for index, holes in enumerate(state):
        if index and holes == state[index - 1]:
            continue
        for residue in {hole % divisor for hole in holes}:
            survivors = tuple(hole for hole in holes if hole % divisor != residue)
            other_children = state[:index] + state[index + 1:]
            if survivors:
                other_children += (survivors,)
            yield tuple(sorted(other_children))


def next_states(state, prime, labels, capacity):
    """Split every live prefix and assign each divisor label at most once."""
    states = {tuple(child for child in state for _ in range(prime))}
    for index, divisor in enumerate(labels):
        remaining = len(labels) - index - 1
        # Each unused label can clear at most one child.
        states = {
            outcome
            for partial in states
            for outcome in remove_class(partial, divisor)
            if len(outcome) <= capacity + remaining
        }
    return states


def minimum_depth(period, prime, holes):
    """Return the least exponent needed, or None if every depth fails.

    Holes are residues modulo period. This exhaustive decision procedure can
    require a large amount of memory, even when the original period is small.
    """
    if period < 1 or period % 2 == 0:
        raise ValueError("the period must be positive and odd")
    if prime < 3 or prime % 2 == 0 or any(prime % d == 0 for d in range(3, isqrt(prime) + 1, 2)):
        raise ValueError("the new factor must be an odd prime")
    if gcd(period, prime) != 1:
        raise ValueError("the new prime must be coprime to the period")
    residues = tuple(sorted({hole % period for hole in holes}))
    if not residues:
        return 0
    labels = divisors(period)
    capacity = (len(labels) - 1) // (prime - 1)
    if capacity == 0:
        return None
    initial = (residues,)
    seen = {initial}
    queue = deque([(initial, 0)])
    while queue:
        state, depth = queue.popleft()
        for successor in next_states(state, prime, labels, capacity):
            if not successor:
                return depth + 1
            if successor not in seen:
                seen.add(successor)
                queue.append((successor, depth + 1))
    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("period", type=int)
    parser.add_argument("prime", help="an odd prime, or 'auto' to consider every fresh odd prime")
    parser.add_argument("holes", type=int, nargs="*")
    args = parser.parse_args()
    try:
        prime = smallest_fresh_prime(args.period) if args.prime == "auto" else int(args.prime)
        depth = minimum_depth(args.period, prime, args.holes)
    except ValueError as exc:
        parser.error(str(exc))
    print("No finite extension" if depth is None else f"Minimum depth: {depth}")

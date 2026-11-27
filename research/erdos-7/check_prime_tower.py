"""Cross-check the state search against direct placements on actual integers."""

from functools import lru_cache
from itertools import combinations

from prime_tower import minimum_depth, smallest_fresh_prime

popcount = getattr(int, "bit_count", lambda n: bin(n).count("1"))


def direct_cover(period, prime, holes, depth):
    modulus = period * prime**depth
    universe = [n for n in range(modulus) if n % period in holes]
    choices = []
    for exponent in range(1, depth + 1):
        for d in range(1, period + 1):
            if period % d:
                continue
            q = prime**exponent * d
            masks = {}
            for index, n in enumerate(universe):
                residue = n % q
                masks[residue] = masks.get(residue, 0) | (1 << index)
            if masks:
                choices.append(tuple(masks.values()))
    choices.sort(key=lambda group: -max(popcount(mask) for mask in group))

    @lru_cache(None)
    def possible(index, uncovered):
        if not uncovered:
            return True
        capacity = sum(max(popcount(mask & uncovered) for mask in group)
                       for group in choices[index:])
        if capacity < popcount(uncovered):
            return False
        # Assigning an unused modulus any residue can only help.
        remaining = {uncovered & ~mask for mask in choices[index]}
        return any(possible(index + 1, rest)
                   for rest in sorted(remaining, key=popcount))

    return possible(0, (1 << len(universe)) - 1)


if __name__ == "__main__":
    comparisons = 0
    for period, prime, points in (
        (9, 5, [0, 1, 3]), (25, 3, [0, 1, 5, 10]),
        (35, 3, [0, 1, 5, 7]), (175, 3, [0, 1, 5, 7]),
    ):
        for count in range(len(points) + 1):
            for holes in combinations(points, count):
                least = minimum_depth(period, prime, holes)
                for depth in range(3):
                    assert direct_cover(period, prime, set(holes), depth) == (
                        least is not None and least <= depth
                    ), (period, prime, holes, depth)
                    comparisons += 1
    assert minimum_depth(25, 3, [0, 5, 10]) == 3
    assert direct_cover(25, 3, {0, 5, 10}, 3)
    assert minimum_depth(25, 3, [-25, 5, 10, 30]) == 3
    assert minimum_depth(25, 3, [0, 1]) is None
    assert [smallest_fresh_prime(m) for m in (1, 3, 45, 105)] == [3, 5, 7, 11]
    print(f"Passed {comparisons + 1} direct finite-depth comparisons.")

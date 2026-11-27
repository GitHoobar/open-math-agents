"""Check the residue theorem on an exact prefix using distinct integer factors."""
from bisect import bisect_right
from math import gcd


def generated_prefix(limit):
    present = bytearray(limit + 1)
    present[2] = present[3] = 1
    earlier = []
    for b in range(2, limit + 1):
        if not present[b]:
            continue
        # In ab-1 the larger factor b is strictly smaller than the output.
        for a in earlier[:bisect_right(earlier, (limit + 1) // b)]:
            present[a*b - 1] = 1
        earlier.append(b)
    return earlier


def check():
    values = generated_prefix(200_000)
    assert values[:7] == [2, 3, 5, 9, 14, 17, 26]
    for m in range(1, 181):
        expected = {x for x in range(m) if m % 3 or x % 3 != 1}
        seen = {n % m for n in values}
        assert seen == expected, (m, expected - seen, seen - expected)
    for a in range(2, 9):
        for b in range(2, 7):
            u = 2**a * 3**b
            k = max(a, b)
            r = 0
            for _ in range(k):
                r = (2*r - 1) % u
            for _ in range(2*k):
                r = (3*r - 1) % u
            s = (3*(r*r - 1) - 1) % u
            assert (r % 4, r % 9, s % 4, s % 9, gcd(r-s, u)) == (1, 5, 3, 8, 6)
    print(f"{len(values)} actual members through 200000; predicted projections for all 180 moduli; 35 reset checks.")


if __name__ == "__main__":
    check()

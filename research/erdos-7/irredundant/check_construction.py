"""Check the covering construction using actual congruence classes and private integers."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod


def crt(*conditions):
    """Return the canonical residue and period for pairwise coprime conditions."""
    value, period = 0, 1
    for residue, modulus in conditions:
        value += period * ((residue - value) * pow(period, -1, modulus) % modulus)
        period *= modulus
    return value, period


@dataclass(frozen=True)
class Progression:
    label: str
    residue: int
    modulus: int
    witness: int

    def contains(self, number):
        return (number - self.residue) % self.modulus == 0


def build(primes):
    primes = tuple(primes)
    if not primes or len(set(primes)) != len(primes) or any(
        q <= 5 or any(q % d == 0 for d in range(2, isqrt(q) + 1)) for q in primes
    ):
        raise ValueError("supply distinct primes greater than five")
    odd_period = 3 * prod(primes)
    holes = [u for u in range(odd_period) if all(u % (3*q) for q in primes)]
    h = len(holes)
    assert h >= 4
    rows = []

    def add(label, conditions, private_coordinates):
        residue, modulus = crt(*conditions)
        binary, five, odd = private_coordinates
        witness, _ = crt((binary, 2**h), (five, 5), (odd, odd_period))
        rows.append(Progression(label, residue, modulus, witness))

    for q in primes:
        add(f"B{q}", [(0, 3*q)], (-1, 4, 3*q))
    for i, hole in enumerate(holes, 1):
        first_zero = 2**(i-1) - 1
        add(f"P{i}", [(first_zero, 2**i)], (first_zero, 4, holes[-1]))
        add(f"C{i}", [(-1, 2**i), (4, 5), (hole, odd_period)], (-1, 4, hole))
    for j in range(1, 5):
        add(f"M{j}", [(-1, 2**j), (j-1, 5)], (-1, j-1, holes[-1]))
    return odd_period, h, rows


def check(primes, enumerate_cells):
    n, h, rows = build(primes)
    assert all(row.modulus > 1 for row in rows)
    assert len({row.modulus for row in rows}) == len(rows)
    for row in rows:
        assert [other.label for other in rows if other.contains(row.witness)] == [row.label]

    neighbors = {row: set() for row in rows}
    pair_weight = Fraction(0)
    for first, second in combinations(rows, 2):
        if gcd(first.modulus, second.modulus) == 1:
            pair_weight += Fraction(1, first.modulus * second.modulus)
            neighbors[first].add(second)
            neighbors[second].add(first)
    assert all(neighbors[row].isdisjoint(neighbors[neighbor])
               for row in rows for neighbor in neighbors[row])
    a = 1 - Fraction(1, 2**h) + Fraction(3, 16)
    b = sum(Fraction(1, 3*q) for q in primes)
    c = (1 - Fraction(1, 2**h)) / (5*n)
    assert sum(Fraction(1, row.modulus) for row in rows) - pair_weight == a+b-a*b+c

    cells = 0
    if enumerate_cells:
        # Membership in each row depends on the first zero binary digit,
        # or on all h digits being one, and on the complete two odd coordinates.
        binary_types = [2**i - 1 for i in range(h)] + [-1]
        for binary in binary_types:
            for five in range(5):
                for odd in range(n):
                    point, _ = crt((binary, 2**h), (five, 5), (odd, n))
                    assert any(row.contains(point) for row in rows)
                    cells += 1
    return len(rows), cells


if __name__ == "__main__":
    for primes, full in [([7], True), ([11], True), ([7, 11], False)]:
        witnesses, cells = check(primes, full)
        print(f"Q={primes}: {witnesses} private integers, exact score checked, {cells} cells enumerated.")

"""Verify a 61-class irredundant odd core and the score bound after completion.

Run with `python3 concrete_example.py`. The CRT checks use ordinary integer
membership tests for every private witness and 127 distinct uncovered residues.
The number h of all uncovered residues modulo the odd period N can be much
larger. The final bound uses h >= 127 and does not enumerate the period.
"""

from fractions import Fraction
from math import gcd, lcm, prod

from check_construction import Progression, crt


def prime_powers(n):
    """Map each prime of n to the full power of that prime dividing n."""
    factors = {}
    p = 2
    while p * p <= n:
        if n % p == 0:
            factors[p] = 1
            while n % p == 0:
                factors[p] *= p
                n //= p
        p += 1
    if n > 1:
        factors[n] = n
    return factors


def full_residue(active, powers, period):
    """Use the specified small integer on the full prime power and zero elsewhere."""
    value, modulus = crt(*((active.get(p, 0), power) for p, power in powers.items()))
    assert modulus == period and 0 <= value < period
    return value


def odd_core():
    moduli = [3 * k for k in range(1, 128, 2) if k % 29 and 3 * k != 315]
    assert len(set(moduli)) == len(moduli) == 61
    period = lcm(*moduli)
    factors = {d: prime_powers(d) for d in moduli}
    full = {}
    for d, powers in factors.items():
        assert prod(powers.values()) == d
        for p, power in powers.items():
            full[p] = max(full.get(p, 1), power)
    assert period == prod(full.values()) and gcd(period, 2 * 29) == 1

    rows = []
    for d in moduli:
        powers = factors[d]
        tail = {p: power for p, power in powers.items() if p != 3}
        if not tail:
            residue_three = powers[3] // 3
        elif len(tail) == 1:
            residue_three = 2 * (powers[3] // 3)
        else:
            assert len(tail) == 2 and powers[3] == 3
            residue_three = 0
        active = {3: residue_three, **{p: power // p for p, power in tail.items()}}
        residue, modulus = crt(*((active[p], power) for p, power in powers.items()))
        assert modulus == d
        witness = full_residue(active, full, period)
        rows.append(Progression(str(d), residue, d, witness))

    for row in rows:
        assert [other.modulus for other in rows if other.contains(row.witness)] == [row.modulus]
    assert full[127] == 127
    holes = {full_residue({127: j}, full, period) for j in range(127)}
    assert len(holes) == 127
    assert all(not row.contains(hole) for hole in holes for row in rows)
    return period, rows, len(holes)


def score_bound(period, rows, verified_holes):
    """Bound the score for the full 29-gate construction using exact fractions.

    Write t = 2^-h. The pure binary rows have mass 1-t; the 28 mixed rows
    have mass g = (1-2^-28)/29. The repairs have mass c = (1-t)/(29N).
    All old moduli share 3, all new moduli are even, and the repair moduli
    are multiples of N. Thus only the old-to-binary and old-to-mixed pairs
    are coprime. Their weight is ab and F = 1 - (a-1)(b-1) + c.
    """
    gate = 29
    mixed = [gate * (1 << i) for i in range(1, gate)]
    assert len(mixed) == 28 and len(set(mixed)) == 28
    assert all(row.modulus % 3 == 0 and period % row.modulus == 0 for row in rows)
    assert all(gcd(2, row.modulus) == 1 for row in rows)
    assert all(gcd(d, row.modulus) == 1 for d in mixed for row in rows)

    g = sum(Fraction(1, d) for d in mixed)
    assert g == (1 - Fraction(1, 1 << 28)) / gate
    b = sum(Fraction(1, row.modulus) for row in rows)
    assert b > Fraction(1001877, 1000000)
    # Since 0 < t <= 2^-127, a-1 = g-t >= this strictly positive lower bound.
    a_excess_lower = g - Fraction(1, 1 << verified_holes)
    assert a_excess_lower > Fraction(1, 30)
    # For every finite h, c = c_sup - t*c_sup < c_sup because t*c_sup > 0.
    c_sup = Fraction(1, gate * period)
    assert c_sup > 0
    upper = 1 - a_excess_lower * (b - 1) + c_sup
    certificate = Fraction(1999869, 2000000)
    assert upper < certificate < 1
    return b, certificate


if __name__ == "__main__":
    n, classes, hole_count = odd_core()
    old_mass, bound = score_bound(n, classes, hole_count)
    print(f"Verified {len(classes)} private residues and {hole_count} distinct holes in the odd core.")
    print(f"N = {n}")
    print(f"b = {old_mass} > 1001877/1000000")
    print(f"The 29-gate completion has F < {bound} = 0.9999345.")

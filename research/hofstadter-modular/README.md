# Which residue classes see Hofstadter’s product-minus-one set?
 
GitHoobar · 27 November 2026 · Research note developed with OpenAI Codex

Start with 2 and 3. Whenever distinct members a and b are available, adjoin ab − 1. Write A for the union of all stages. The open question studied here is whether |A ∩ [1,X]| / X converges. Korsky proved that its lower limit is positive. The convergence question appears separately in the Formal Conjectures catalogue. The proofs below establish a structural result about A and identify a limitation of the congruence approach. [Lower-density theorem](https://arxiv.org/abs/2608.07910) · [Open convergence statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/424.lean#L81)

## The modular result

**Theorem.** For every positive integer m, the set A meets every residue class modulo m if 3 does not divide m. If 3 divides m, it meets precisely the residues that are 0 or 2 modulo 3. In each class it meets, A contains an increasing affine image of all but finitely many members of A. In particular each such class contains a subset of A of positive lower natural density, measured among all positive integers.

The exclusion modulo 3 was already known. The assertion proved here is that the list is exhaustive, simultaneously for arbitrary composite moduli, and that each surviving class contains the stated affine copy. We make no priority claim for this lemma. [Known exclusion and attribution](https://www.erdosproblems.com/424)

### Proof of the residue description

The residues 0 and 2 modulo 3 contain the seeds and are closed under the rule. Call a class modulo m *admissible* if it is compatible with one of those two residues.

It suffices to prove the result for moduli M divisible by 36. For arbitrary m use M = lcm(m,36). Every admissible class modulo m lifts to an admissible one modulo M by the Chinese remainder theorem. Write M = uv, where u = 2ᵃ3ᵇ with a,b at least 2 and gcd(v,6) = 1. We identify a residue modulo M with its two coordinates modulo u and v.

Write Fⱼ(x) = jx − 1. The maps F₂ and F₃ can be applied to any element of A greater than 3 and increase it. Modulo v they are permutations. The orbit of 5 under their compositions is the entire residue ring modulo v: the orbit is finite and stable under each permutation and its inverse, and F₂F₃(x) = 6x − 3 differs from F₃F₂(x) = 6x − 4 by 1. Thus the orbit is stable under translation by 1. Each of its residues has arbitrarily large actual representatives in A. Indeed, repeating a positive power of F₂ that is the identity modulo v preserves the residue and increases the representative. The argument includes v = 1.

Let B consist of those residues w modulo u for which **every** pair (w,y), y modulo v, has infinitely many representatives in A. B is stable under F₂ and F₃ since 2 and 3 are units modulo v. Also, w,z in B imply wz − 1 in B. To obtain the desired second coordinate y, use representatives with second coordinates 1 and y+1. The infinite supplies allow the actual integers to be distinct and their product to be arbitrarily large, even when w = z. This detail enforces Hofstadter’s distinct-factor rule.

We construct a member r of B. Choose k ≥ max(a,b). Apply F₂ exactly k times and then F₃ exactly 2k times to the orbit representatives above. The composite has slope 2ᵏ3²ᵏ, a multiple of u and a unit modulo v. The first coordinate therefore becomes a constant r, and all second coordinates are retained. We have r ≡ 1 modulo 4 since F₂ᵏ(x) = 1 + 2ᵏ(x−1) and F₃²(x) = 9x−4 preserves the residue modulo 4. Also r ≡ 5 modulo 9 since F₃²(x) ≡ 5 modulo 9.

Now s = 3(r²−1)−1 belongs to B by closure. Since r is odd, s ≡ 3 modulo 4. Since r ≡ 5 modulo 9, s ≡ 8 modulo 9. Both r and s are units modulo u and gcd(r−s,u) = 6. On B the maps Fᵣ and Fₛ are permutations: closure gives inclusion, and multiplication by a unit gives injectivity on a finite set. The two orders of composition have the same slope rs and constant terms differing by s−r. Therefore B is stable under translation by s−r. This translation generates precisely the multiples of 6 modulo u.

Finally r, r²−1, F₂(r), and F₃(r) belong to B and represent the four classes 5, 0, 3, and 2 modulo 6. Adding multiples of 6 fills every admissible class modulo u. The definition of B supplies every second coordinate. This proves the residue description and infinitude of witnesses.

### Affine copies and positive density in each class

Fix an admissible residue t modulo m. Both 0 and −t−1 are admissible. Choose d,b in A with d ≡ 0 and b ≡ −t−1 modulo m. For every sufficiently large x in A, the two applications of the rule give

    L(x) = b(dx−1)−1 ∈ A,       L(x) ≡ t (mod m).

In particular x differs from d and dx−1 differs from b. The slope bd is positive. If δ is the lower natural density of A, then the lower density of its members congruent to t is at least δ/(bd), by counting x up to (X+b+1)/(bd). Korsky’s theorem supplies δ > 0. The bound depends on the class.

## What this proves about the attempted approach

A periodic set containing A must have density at least 2/3. For a period not divisible by 3 it must contain every residue, and for one divisible by 3 it must contain every admissible residue. The set of integers congruent to 0 or 2 modulo 3 attains 2/3. Hence **2/3 is exactly the infimum of the densities of periodic supersets of A**. Finite combinations of congruence exclusions alone cannot improve it. Whether the counting ratio itself converges remains open.

We tried to pass from local abundance to global coverage by products. The following obstruction explains why that passage requires another property of the recursion. Let Ω(n) count prime factors with multiplicity. Define B₀ to consist of the admissible integers with even Ω. In every admissible progression, B₀ has positive lower density. Indeed, refine the progression to an admissible class modulo lcm(m,3), and take a prime p congruent to 1 modulo that modulus by Dirichlet’s theorem. The two integers n and pn stay in the class and have opposite Ω parity. Counting n up to X/p, with any output counted at most twice, gives positive lower density for both parities.

Nevertheless B₀·B₀−1 misses an entire positive-lower-density subset of the admissible integers: take n ≡ 0 modulo 3 with Ω(n+1) odd. There are positively many in the lower-density sense by the same parity argument on n+1 ≡ 1 modulo 3. A product of two members of B₀ always has even Ω. This comparison rules out inferring near-total product coverage merely from positive density in every admissible progression. B₀ is a comparison set and does not satisfy Hofstadter’s generating rule. The missing step for A is control of factor membership together with its correlations across scales.

## Verification

Run `python3 -B check.py` from this directory. The program constructs the exact prefix by processing the larger of two distinct integer factors in increasing order. Both inputs of each operation are smaller than its output, so this order misses no member of the prefix. It found 83,779 actual members through 200,000 and verified every predicted projection for moduli 1 through 180. It also checked the reset residues and gcd calculation on 35 pairs of prime-power exponents. These checks supplement the general proof. This note has not been peer reviewed or formalized in Lean.

[Literature and selection record](./search.md) · [Reproducible check](./check.py)

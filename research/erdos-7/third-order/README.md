# A third-order bound for unions of odd residue classes

**GitHoobar, 27 November 2026. Developed with OpenAI Codex.**

Choose one residue class for each divisor greater than one of any odd period. How much of the period can those classes cover? The manuscript proves the proposed upper bound that uses only the sizes of the classes and the intersections belonging to coprime pairs and pairwise-coprime triples. It holds for arbitrarily many prime factors and arbitrary prime powers. [Read the manuscript (PDF)](./third-order-crt.pdf) · [LaTeX source](./third-order-crt.tex)

## The question and the result

Let $A_j$ be the sum of $1/(d_1\cdots d_j)$ over unordered, pairwise-coprime sets of $j$ distinct nontrivial divisors. The fraction of residues covered by **any** assignment is at most $A_1-A_2+A_3$. A value below one certifies that some residues escape every assignment. The bound depends only on the period, so it can be computed before any residues are chosen.

Hackmon introduced the three-term expression. Toker proved its coverage bound for periods with at most seven different prime factors. Section 5 of Toker's November memorandum explicitly left the inequality at unrestricted rank unestablished. The same paper gave counterexamples to replacing the three terms by the unrestricted alternating sum. Our proof shows that the full sum also bounds coverage whenever the three-term bound is strictly below one. Erdős problem 7, which asks whether a distinct odd covering exists at all, remains open. [Hackmon, Definition 2 and §7](https://rxiv.org/pdf/2604.0035v1.pdf) · [Toker, §§4–5](https://doi.org/10.5281/zenodo.23927150) · [Erdős problem 7](https://www.erdosproblems.com/7)

## How the proof works

The sum of the reciprocals of the positive powers of any odd prime is at most one half. This places the contribution of every prime in the same interval, independently of how many primes there are. Two polynomial inequalities on that interval show that whenever the proposed bound is informative, the total weight of all classes is below five. This makes the fourth and subsequent terms of the alternating sum decrease in magnitude. A deletion identity passes positivity from complete divisor families to arbitrary subfamilies. A short proof of Shearer's avoidance inequality then gives the desired coverage bound. All steps appear in the manuscript.

## Research and verification record

- We checked the formulation against Hackmon's Definition 2 and Toker's displayed equations (5.1)–(5.4). A search of work attributed to Hackmon and Toker, DataCite records, and indexed work on the CRT coverage maximality question through 27 November 2026 found the through-seven result and the all-orders counterexamples. We found no earlier proof of this unrestricted three-term bound. This is a dated search result, not a guarantee of priority.
- The cube inequalities have two independent derivations. The manuscript uses the shorter one, by evaluating separately affine functions at the vertices. The counting argument and the probability argument are included so the proof can be checked without trusting a computation.
- Lean verifies the [two polynomial inequalities](./ThirdOrderBounds.lean), the [weighted counting and alternating-tail estimate](./ThirdOrderTail.lean), [positivity under deletion](./ThirdOrderDeletion.lean), [the finite-event form of Shearer's argument](./ThirdOrderAvoidance.lean), and [the exact CRT independence counts](./ThirdOrderCRT.lean). The manuscript gives the full arithmetic proof.
- The [integer-arithmetic calculator](./coverage_bound.py) evaluates the bound directly from the prime powers of the period. Its values agreed with direct coprime-pair and coprime-triple enumeration for all 1,000 odd periods below 2,000. To reproduce the example in the paper, run `python3 coverage_bound.py 15015`. It certifies at least 2,905 uncovered residues.
- A related potential disproof of the all-orders claim was discarded after we located Toker's prior result. The earlier one-prime repair work on Erdős problem 7 has its own [research record](../README.md).

This is a public research manuscript awaiting independent mathematical review.

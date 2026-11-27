# Can distinct odd residue classes cover the integers?

**GitHoobar · 27 November 2026 · developed with OpenAI Codex.** Can a finite family of residue classes with distinct odd moduli greater than one cover every integer? We prove a sufficient condition for turning a partial cover into a full cover and verify the construction in Lean. We also give a counterexample to a lemma in a proposed impossibility proof. The unresolved step is to exhibit an odd partial cover satisfying our condition. [Erdős Problems](https://www.erdosproblems.com/7) · [Left to Solve’s precise Lean target](https://lefttosolve.com/p/Erdos7.erdos_7/agent.txt)

## Where a proposed nonexistence proof fails

Lemma 3.2 in Giovanni Esposito’s preprint asserts that if the available distinct divisors of an odd integer $M$ cannot cover a subset $U$ modulo $M$, adjoining a fresh odd prime $p$ cannot cover the inverse image of $U$ modulo $pM$. The following witness disproves this implication as stated. [Preprint and PDF, §3](https://zenodo.org/records/18440762)

Take $M=25$ and $U=\{0,1,2\}$ modulo 25. The two available moduli are 5 and 25. Each class for either modulus contains at most one of the three points. Now adjoin $p=3$ and use these five classes.

| Class | What it covers in the inverse image of $U$ |
| --- | --- |
| $0\pmod 5$ | Every point above 0 modulo 25 |
| $1\pmod{25}$ | Every point above 1 modulo 25 |
| $0\pmod 3$ | The point above 2 whose residue modulo 3 is 0 |
| $7\pmod{15}$ | The point above 2 whose residue modulo 3 is 1 |
| $2\pmod{75}$ | The point above 2 whose residue modulo 3 is 2 |

All five moduli are distinct, odd and greater than one. The old classes work in **every** slice modulo 3. The classes with a factor of 3 only need to cover the points the old classes missed in each slice. This distinction is where the inference from base insufficiency breaks down. The integer 4 escapes all five classes, which explicitly verifies that this witness leaves the prize question open.

## A construction for a fixed partial cover

Let $M>1$ be odd. Fix some residue classes whose distinct, nontrivial moduli divide $M$. Let $H\subseteq\mathbb Z/M\mathbb Z$ be the uncovered residues, let $h=|H|>0$, and let $p$ be an odd prime coprime to $M$. We keep all the chosen classes fixed.

**Exact criterion for one extension.** A completion using new divisors of $pM$ divisible by $p$ exists if and only if there are $p-1$ covers of $H$ using classes modulo nontrivial divisors of $M$, such that no divisor occurs more than once across the entire collection of covers. We may always use the modulus $p$ to cover one whole slice. For each other slice, a class modulo $pd$ restricts to one class modulo $d$. Conversely, the Chinese remainder theorem (CRT) combines any chosen residue modulo $d$ with its assigned slice modulo $p$ to produce a class modulo $pd$. Distinct divisor labels give distinct new moduli. An old modulus $d$ and a new modulus $pd$ can both occur.

**Sufficient condition allowing higher powers.** Write $B=\tau(M)-1$, the number of nontrivial divisors of $M$. If

$$
B>(p-2)h,
$$

then a finite sequence of new classes with moduli $p^j d$, where $j\ge1$ and $d\mid M$, completes the cover. For comparison, a single extension suffices when $B\ge (p-1)h$, by assigning an individual divisor label to every hole in each of the $p-1$ slices.

To prove the stronger condition, keep the remaining holes in a single class modulo $p^{j-1}$. Initially $j=1$, so this is automatic. Suppose there are $s$ remaining base residues in that class. Splitting it into classes modulo $p^j$ produces $p$ copies of those $s$ holes. Use modulus $p^j$ for one entire child. Use $(p-2)s$ distinct nontrivial divisors $d$ to cover the next $p-2$ children, assigning one $p^j d$ class by CRT per hole. Spend the remaining labels on distinct holes in the last child. This leaves at most $\max(0,(p-1)s-B)$ holes, all in that child. As $B>(p-2)s$, this is strictly fewer than $s$. At the next depth all $p^{j+1}d$ are fresh because $p\nmid M$. Repetition stops after at most $h$ depths.

There is a matching obstruction for certain hole sets. Suppose that for **every** nontrivial $d\mid M$, the holes are pairwise distinct modulo $d$. Give each base hole mass 1, spread uniformly over its refinements in the $p$-coordinate. At depth $j$ the single class of modulus $p^j$ covers at most $h/p^j$ mass. Each of the $B$ other moduli $p^j d$ covers at most $1/p^j$. Up to any finite depth $J$, their combined mass is at most

$$
(h+B)\sum_{j=1}^J p^{-j} < \frac{h+B}{p-1}.
$$

Covering the whole mass $h$ therefore requires $B>(p-2)h$. This proves sharpness for that class of hole sets when the permitted additions have the specified form. It leaves open whether any eligible starting family satisfies the sufficient condition.

McNew and Setty proved that a period with one missing residue can be completed by adjoining a prime larger than its prime factors and at most its divisor count. For one hole our inequality likewise reads $p\leq\tau(M)$. Our construction permits any coprime odd prime and any positive number of holes satisfying the inequality. The method of dividing a covering into slices along a prime also has precedents. We make no claim of historical priority for a prime-slicing technique. [McNew and Setty, Corollary 4.8](https://www.nathanmcnew.com/covering.pdf) · [Dalton and Trifonov, Lemmas 6 and 10](https://cs.uwaterloo.ca/journals/JIS/VOL25/Trifonov/trif3.pdf)

**A consequence for periods missing both 3 and 5.** Suppose $M$ is odd and coprime to 15. Every partial cover using distinct nontrivial divisors of $M$ leaves **at least $\tau(M)-1$ residue classes uncovered**. Indeed, Dai, Li, Li and Yi's Theorem 1.1 requires every full odd distinct cover to have period divisible by 5. A full base cover would already contradict this. If the positive hole count were smaller than $\tau(M)-1$, use our construction with $p=3$. Its period divides $3^hM$, still coprime to 5, giving the same contradiction. This corollary uses the stated result of their November 2026 preprint as an external theorem. [Dai, Li, Li and Yi, Theorem 1.1](https://arxiv.org/abs/2611.15110)

**When the prime is large relative to the number of divisor labels.** Let $D=\tau(M)$. If $D\le 2(p-1)$, a fixed nonempty set of holes $H$ can be covered using finitely many $p^j d$ classes ($j\ge 1$, $d\mid M$) exactly when there are $p-2$ covers of $H$ by nontrivial divisors of $M$ that use disjoint divisor labels and leave at least one label unused. Here a label specifies one divisor and permits a single choice of its residue in the entire layer.

For necessity, let $k$ count the residues modulo $p^j$ with any surviving holes after all classes through level $j$ have been placed. Each such residue has $p$ children. There are only $D$ new labels, and one class touches only one child. The next count is therefore at least $pk-D$. Once $k\ge 2$ this is at least $k$, so a finite completion keeps exactly one surviving residue until the final level. Consider the first level where that survivor's hole set shrinks or disappears. The other children all started with the original $H$ and have been covered completely. At most one of them used the pure $p$-power label. That yields $p-2$ disjoint nontrivial covers. A further nontrivial divisor hits the shrinking child, or covers part of another whole child if all children close. Conversely, at every level use the pure power for one child and the $p-2$ disjoint covers for as many children. The spare label removes a nominated hole in the last child. The converse works for any $D$. This characterization has a written proof here. Its general necessity is asserted only in the displayed range.

## Testing a published starting family

Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong construct a covering in which modulus 9 occurs three times. Theorem 3.1 explains that keeping just one occurrence gives a distinct-modulus family covering every integer outside $S=\{3,6\pmod 9\}$. Some points of $S$ may already be covered. The construction uses both 3 and 9. [Journal PDF, Theorem 2.5 on p. 3, Figure 7 on p. 5, and Theorem 3.1 on p. 8](https://faculty.kutztown.edu/wong/DM349%282026%29.pdf)

We tried to cover all of $S$ with new distinct moduli built from 3 and one fresh prime $q\ge5$. Normalize natural density so that $S$ has mass 1. Moduli $3^a$ for $a\ge3$ have total capacity at most $\sum_{a\ge3}9/(2\cdot3^a)=1/4$. For a fixed exponent $b\ge1$, the moduli $q^b$ and $3q^b$ contribute at most $1/q^b$ each. Summing over $3^a q^b$ for $a\ge2$ contributes at most $3/(4q^b)$. Even allowing all these powers and ignoring overlaps gives an upper bound of $1/4+11/(4(q-1))\le15/16$. This rules out filling the two entire progressions by this method. It leaves the actual, potentially smaller, hole set and extensions with several primes as separate possibilities.

## Reproducing the Lean checks

The [prime-extension counterexample](./PrimeExtension.lean) uses the Lean standard library. The [repair construction](./OddLift.lean) proves the full Chinese remainder construction, including distinctness of every new modulus and coverage of negative integers. The [reduction](./OddReduction.lean) shows that any qualifying partial cover, combined with that repair theorem, implies the exact upstream statement in terms of ideals of the integers. The repair theorem is uniform in the period, the new prime and the list of holes.

```sh
lean +leanprover/lean4:v4.33.1 PrimeExtension.lean
```

For the other files, use the [pinned formal-conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53) with its Mathlib cache. From its root, run the following with the paths to the downloaded files.

```sh
lake build 'FormalConjectures.ErdosProblems.«7»'
lake env lean /path/to/OddLift.lean
lake env lean /path/to/OddReduction.lean
```

The kernel reports only axioms drawn from `propext`, `Classical.choice`, and `Quot.sound`. The mass bound and the calculation for the Bispels family have written proofs above. The existential seed hypothesis is an input to the reduction and remains open.

## Status and historical rewards

The November 2026 preprint of Dai, Li, Li and Yi reports that any odd distinct covering system has least common multiple divisible by 45 and minimum modulus at most 9. Both conclusions are necessary conditions. [Author preprint](https://arxiv.org/abs/2611.15110)

Filaseta, Ford and Konyagin record Erdős’s offer of $25 for proving nonexistence and Selfridge’s offer, raised to $2,000, for the first explicit construction. We could verify the historical offers in their paper. The Combinatorics Foundation requires documentation of the reward in a publication by Erdős as well as a solution accepted by the mathematical community and published in a reputable peer-reviewed mathematics journal. We did not locate the $25 offer in Erdős’s own checked passages or confirm a current payer for Selfridge’s offer. This attempt earned no reward. [Historical account, p. 1 of author copy](https://www.ford126.web.illinois.edu/wwwpapers/ffk.pdf) · [Foundation rules](https://www.combinatoricsfoundation.org/erd%C5%91s-problems)

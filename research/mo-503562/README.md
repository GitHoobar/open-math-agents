# The exact variable factors of a union determinant

**GitHoobar · 27 November 2026 · developed with OpenAI Codex**

Fabius Wiesner asked which powers of the variables divide a determinant built from a union-closed family of sets. The answer is exactly the frequency of each element. This part holds for **every finite family of distinct finite sets**. Union closure gives a product formula and a probability interpretation for the remaining polynomial. [Wiesner’s question and examples on MathOverflow](https://mathoverflow.net/questions/503562/determinant-related-to-a-union-closed-family-of-sets)

## Why the exponents are exact

Write $x^S=\prod_{i\in S}x_i$, including $x^\varnothing=1$. Index rows and columns by the members of a finite family $\mathcal F$. Its matrix has entries $M_{A,B}=x^{A\cup B}$.

Factor $x^A$ out of row $A$. As Zach Teitler observed in the question’s comments, these factors already supply the claimed powers. If $f(i)$ counts the sets containing $i$, the residual determinant is

$$
\det M=\left(\prod_i x_i^{f(i)}\right)P(x),
\qquad
P(x)=\det\bigl[x^{B\setminus A}\bigr]_{A,B\in\mathcal F}.
$$

The decisive observation is **$P(0)=1$**. At zero the entry in row $A$ and column $B$ is one precisely when $B\subseteq A$. Order the sets by increasing cardinality, breaking ties arbitrarily. Every strict subset occurs earlier, so the resulting matrix is lower triangular with ones on the diagonal. A polynomial divisible by any $x_i$ vanishes at the origin. Thus every displayed exponent is exact, simultaneously. [Original question and prior comment](https://mathoverflow.net/questions/503562/determinant-related-to-a-union-closed-family-of-sets)

## A closed formula for the quotient

Assume now that $\mathcal F$ is closed under unions. Let $\mu$ be the Möbius function of its inclusion order. The following product specializes the classical semilattice determinant theorem, applied in the dual order. [Altınışık, Sagan and Tuğlu, Theorem 3.1](https://arxiv.org/abs/math/0406155)

$$
P(x)=\prod_{A\in\mathcal F}
\left(\sum_{B\in\mathcal F\, :\, B\supseteq A}
      \mu(A,B)\,x^{B\setminus A}\right).
$$

To see the factorization directly, put $w(A)=\sum_{B\supseteq A}\mu(A,B)x^B$ with sums over the family. Möbius inversion gives $x^C=\sum_{B\supseteq C} w(B)$. Define $Z_{A,B}=\mathbf1_{A\subseteq B}$. The $(A,B)$ entry of $Z\operatorname{diag}(w)Z^\mathsf T$ is $\sum_{C\supseteq A\cup B} w(C)=x^{A\cup B}$, since the union belongs to the family. Also $\det Z=1$. Taking determinants and extracting $x^A$ from each factor $w(A)$ gives the formula.

For the chain $\{1\}\subset\{1,2\}\subset\{1,2,3\}$ the successive factors are $1-x_2$, $1-x_3$ and $1$. Thus the quotient is $(1-x_2)(1-x_3)$, agreeing with Wiesner’s chain example.

## What each factor counts

Take $0\le x_i\le1$. Starting from $A$, include each element $i$ outside $A$ independently with probability $x_i$, producing a random superset $T$. The factor indexed by $A$ is the probability that **$A$ is the largest member of the family between $A$ and $T$**.

Indeed, the union $U$ of all the family members in that interval belongs to the family and lies inside $T$. The sum $\sum_{A\subseteq B\subseteq U}\mu(A,B)$ equals $1$ when $U=A$ and $0$ otherwise. Taking expectations gives the displayed factor because $\Pr(B\subseteq T)=x^{B\setminus A}$ for $B\supseteq A$. If a separate independent choice of $T$ is made for each $A$, then $P(x)$ is the probability that the event holds for all of them.

## Lean verification

[UnionDeterminant.lean](./UnionDeterminant.lean) proves the frequency factorization, constant term one, and nondivisibility for arbitrary injectively indexed families over a finite ground set. [UnionMobius.lean](./UnionMobius.lean) verifies the product formula for union-closed families using Mathlib’s integer Möbius function. Both proofs use only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. The probability interpretation has the written proof above.

With the Mathlib cache installed, run the following from the [pinned formal-conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53), passing the path to the downloaded Lean file.

```sh
lake env lean /path/to/UnionDeterminant.lean
lake env lean /path/to/UnionMobius.lean
```

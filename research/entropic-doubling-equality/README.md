# Equality in the Gaussian large-doubling bound

GitHoobar · 27 November 2026 · Developed with OpenAI Codex

Gavalakis, Kontoyiannis and Madiman ask whether equality in their large-doubling inequality characterizes the Gaussian when the input has finite differential entropy. For an independent nondegenerate Gaussian perturbation, the answer is yes, in every dimension. The classical entropy power inequality and the Gaussian maximum-entropy principle give a short proof.

## Statement

Let X have finite second moments and finite differential entropy h(X) in dimension d ≥ 1. Let X′ be an independent copy and let Z be an independent Gaussian vector. Write K and C for the covariance matrices of X and Z. The density of X implies K is positive definite. Set

    N(Y) = exp(2h(Y)/d),     S = (X + X′)/√2,
    σ[X] = N(S)/N(X),     a = (det C / det K)^(1/d).

If C is positive definite, equality in the following inequality holds precisely when X is Gaussian and C is a positive scalar multiple of K.

    h(X + Z) − h(X) ≥ (d/2) log(1 + a σ[X]).                    (1)

## Proof

Let G be Gaussian with the same mean and covariance as S. Independence gives Cov(S) = K. Among laws of this covariance the Gaussian maximizes entropy, so N(S) ≤ N(G). The Gaussian entropy formula gives N(Z) = a N(G). By the entropy power inequality for independent summands,

    N(X + Z) ≥ N(X) + N(Z) ≥ N(X) + a N(S).                  (2)

Taking logarithms gives (1). All quantities are finite and positive. Finite covariance bounds entropy from above, and the entropy power inequality bounds the entropies of the sums from below.

Equality in (1) forces equality at both steps of (2). Equality at the first step of (2) in the classical vector entropy power inequality forces Gaussian summands with proportional covariances. Conversely, for Gaussian X and C = tK with t > 0, one has σ[X] = 1, a = t and N(X + Z) = (1+t)N(X). This proves both directions.

## A check using the second step alone

Equality at the second step forces S to be Gaussian by uniqueness of the entropy maximizer. After centering, the characteristic function φ of X then satisfies φ(u)² = exp(−uᵀKu) for all u. The continuous ratio φ(u)/exp(−uᵀKu/2) takes values in {−1,1} and equals 1 at zero. It is identically 1, so X is Gaussian. To check proportionality, let λ₁,…,λd be the eigenvalues of the covariance of Z after whitening X. Gaussian equality becomes

    (∏ (1 + λᵢ))^(1/d) = 1 + (∏ λᵢ)^(1/d).

Strict convexity of s ↦ log(1 + exp(s)), applied to s = log λᵢ, gives equality exactly when all λᵢ coincide. This also proves the equality claim using only the inequality part of the entropy power inequality.

## Singular Gaussian noise

If C is singular, then a = 0. The entropy gap in (1) is h(X + Z) − h(X) = I(Z; X + Z), since conditioning on Z translates X. The output has a density, finite covariance, and finite entropy by concavity of entropy under mixtures of translates together with the Gaussian entropy upper bound. Zero mutual information would make Z and X + Z independent, forcing their cross-covariance to vanish. This cross-covariance is C. Thus the gap is strictly positive for every nonzero singular C. When C = 0 the noise is deterministic and equality holds for every allowed input.

## A quantitative consequence

For positive definite C define the power deficit Δ = N(X + Z) − N(X) − a N(S). The second step of (2) and the identity D(S ∥ G) = h(G) − h(S) give

    Δ / N(Z) ≥ 1 − exp(−2D(S ∥ G)/d).

Here D is relative entropy and G matches the mean as well as the covariance of S. In particular, if Δ ≤ ε N(Z) with 0 ≤ ε < 1, then D(S ∥ G) ≤ −(d/2) log(1−ε). This controls the normalized sum of two copies of X directly in terms of the power deficit.

## Sources

[1] L. Gavalakis, I. Kontoyiannis and M. Madiman. The entropic doubling constant and robustness of Gaussian codebooks for additive-noise channels. IEEE Transactions on Information Theory 70 (2024), 8467–8477. The question appears after Theorem 5, equation (10), in §3.2 of the authors’ revised manuscript. https://arxiv.org/pdf/2403.07209v2#page=11

[2] A. Dembo, T. M. Cover and J. A. Thomas. Information theoretic inequalities. IEEE Transactions on Information Theory 37 (1991), 1501–1518. https://isl.stanford.edu/~cover/papers/dembo_cover_thomas_91.pdf

[3] L. Gavalakis and I. Kontoyiannis. Conditions for equality and stability in Shannon’s and Tao’s entropy power inequalities. The authors treat equality in Shannon’s inequality under weaker moment assumptions. https://arxiv.org/abs/2509.14021

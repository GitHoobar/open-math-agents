import OMAStatements.S_oeis_a345680

/-!
Arbitrarily long intervals reaching zero under alternating decimal digit squares.
Proof by GitHoobar with OpenAI Codex, November 2026. The imported statement is
by rpabani, following Stephen Cross's OEIS A345680. The proof uses base-100
concatenation to lift good translates, a finite kernel-verified certificate
to seed the induction, and a strict interval contraction above the seed.
-/

open OMA.S_oeis_a345680

namespace AlternatingDigitSquares

private def D (n : ℕ) : ℤ :=
  ((Nat.digits 10 n).map fun d => (d : ℤ)^2).alternatingSum

private theorem zeroD : D 0 = 0 := by simp [D]

private theorem digit (n : ℕ) : D n = ((n % 10 : ℕ) : ℤ)^2 - D (n / 10) := by
  by_cases h : n = 0
  · simp [h, zeroD]
  · unfold D
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) h]
    simp

private def weight (r : ℕ) : ℤ :=
  ((r % 10 : ℕ) : ℤ)^2 - ((r / 10 : ℕ) : ℤ)^2

private theorem pair (q r : ℕ) (hr : r < 100) :
    D (100*q+r) = D q + weight r := by
  conv_lhs => rw [digit, digit ((100*q+r)/10)]
  have h₁ : (100*q+r)%10 = r%10 := by omega
  have h₂ : (100*q+r)/10%10 = r/10 := by omega
  have h₃ : (100*q+r)/10/10 = q := by omega
  rw [h₁,h₂,h₃]; unfold weight; ring

private theorem concat (p q r : ℕ) (hr : r < 100^p) :
    D (100^p*q+r) = D q + D r := by
  induction p generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    simp [this, zeroD]
  | succ p ih =>
    have he : 100^(p+1)*q+r = 100*(100^p*q+r/100)+r%100 := by
      rw [pow_succ]; nlinarith [Nat.mod_add_div r 100]
    have hl : r/100 < 100^p := by rw [pow_succ] at hr; omega
    have h := pair (r/100) (r%100) (by omega)
    rw [show 100*(r/100)+r%100=r by omega] at h
    rw [he, pair _ _ (by omega), ih _ hl, h]; ring

private theorem posPrefix (t : ℕ) : ∃ q, D q = (t : ℤ) := by
  induction t with
  | zero => exact ⟨0, zeroD⟩
  | succ t ih =>
    obtain ⟨q,h⟩ := ih
    refine ⟨100*q+1, ?_⟩
    rw [pair _ _ (by decide), h]; norm_num [weight]

private theorem signedPrefix (z : ℤ) : ∃ q, D q = z := by
  cases z with
  | ofNat t => exact posPrefix t
  | negSucc t =>
    obtain ⟨q,h⟩ := posPrefix (t+1)
    refine ⟨10*q, ?_⟩
    rw [digit, show 10*q%10=0 by omega, show 10*q/10=q by omega,h]
    omega

private def Good (S : Set ℕ) : Prop := ∃ k : ℕ, ∀ x ∈ S, IsTerm (k+x)

/-- An offset in the signed digit sum can be supplied by a common high prefix. -/
private theorem transfer {S T : Set ℕ} (c p : ℕ) (v : ℤ)
    (h : ∀ x ∈ S, x+c < 100^p ∧ 0 ≤ D (x+c)+v ∧ (D (x+c)+v).toNat ∈ T)
    (ht : Good T) : Good S := by
  obtain ⟨k,hk⟩ := ht
  obtain ⟨q,hq⟩ := signedPrefix ((k:ℤ)+v)
  refine ⟨100^p*q+c, ?_⟩
  intro x hx
  obtain ⟨hb,hpos,hmem⟩ := h x hx
  obtain ⟨j,hj⟩ := hk _ hmem
  refine ⟨j+1, ?_⟩
  rw [Function.iterate_succ_apply]
  have hd : D (100^p*q+c+x) = ((k+(D (x+c)+v).toNat : ℕ) : ℤ) := by
    rw [show 100^p*q+c+x=100^p*q+(x+c) by omega, concat _ _ _ hb,hq]
    push_cast; rw [Int.toNat_of_nonneg hpos]; ring
  change f^[j] (D (100^p*q+c+x)).natAbs = 0
  simpa only [hd, Int.natAbs_natCast] using hj

private theorem split (n : ℕ) : D n = D (n/100) + weight (n%100) := by
  have h := pair (n/100) (n%100) (by omega)
  rwa [show 100*(n/100)+n%100=n by omega] at h

private def four (n : ℕ) : ℤ := weight (n/100) + weight (n%100)

private theorem four_eq (n : ℕ) (h : n < 10000) : D n = four n := by
  rw [split n, split (n/100), show n/100/100=0 by omega,
    show n/100%100=n/100 by omega, zeroD, zero_add]
  rfl

/-- Replay a certificate on one offset. Each step checks its range before continuing. -/
private def accept : List (ℕ × ℤ) → ℕ → Bool
  | [], x => decide (x = 0)
  | (c,v)::rest, x =>
    let y := four (x+c) + v
    decide (x+c < 10000) && decide (0 ≤ y) && accept rest y.toNat

private theorem accepted_good (s : List (ℕ × ℤ)) : Good {x | accept s x = true} := by
  induction s with
  | nil =>
    refine ⟨0, ?_⟩
    intro x hx
    have he : x = 0 := of_decide_eq_true hx
    exact ⟨0, by simp [he]⟩
  | cons cv rest ih =>
    obtain ⟨c,v⟩ := cv
    apply transfer c 2 v _ ih
    intro x hx
    change accept ((c,v)::rest) x = true at hx
    simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨hb,hpos⟩,hm⟩ := hx
    rw [four_eq _ hb]
    exact ⟨hb,hpos,hm⟩

private def certificate : List (ℕ × ℤ) :=
  [(990,82),(195,77),(19,81),(981,82),(430,65),(739,23),(833,-1),(148,44),
   (862,1),(973,10),(869,-77),(21,25),(11,15),(88,0),(0,1),(5,-25),(0,0)]

private theorem seed : Good {x | x ≤ 200} := by
  have check : ∀ i : Fin 201, accept certificate i.val = true := by decide +kernel
  obtain ⟨k,h⟩ := accepted_good certificate
  exact ⟨k, fun x hx => h x (check ⟨x, by change x ≤ 200 at hx; omega⟩)⟩

private theorem crude (n : ℕ) : -(9*(n:ℤ)) ≤ D n ∧ D n ≤ 9*(n:ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz,zeroD]
    obtain ⟨ha,hb⟩ := ih (n/10) (by omega)
    have h₁ : ((n%10 : ℕ):ℤ) ≤ 9 := by omega
    have h₂ : 0 ≤ ((n%10 : ℕ):ℤ) := by positivity
    have h₃ : ((n%10 : ℕ):ℤ)^2 ≤ 9*((n%10 : ℕ):ℤ) := by nlinarith
    have h₄ : (n:ℤ) = 10*((n/10 : ℕ):ℤ) + ((n%10 : ℕ):ℤ) := by omega
    rw [digit n]
    constructor <;> nlinarith [sq_nonneg ((n%10 : ℕ):ℤ)]

private theorem bound (n : ℕ) :
    -(9*((n/100 : ℕ):ℤ)+81) ≤ D n ∧ D n ≤ 9*((n/100 : ℕ):ℤ)+81 := by
  obtain ⟨ha,hb⟩ := crude (n/100)
  have h₁ : ((n%100%10 : ℕ):ℤ) ≤ 9 := by omega
  have h₂ : ((n%100/10 : ℕ):ℤ) ≤ 9 := by omega
  have h₃ : 0 ≤ ((n%100%10 : ℕ):ℤ) := by positivity
  have h₄ : 0 ≤ ((n%100/10 : ℕ):ℤ) := by positivity
  rw [split n]; unfold weight
  constructor <;> nlinarith [sq_nonneg ((n%100%10 : ℕ):ℤ),
    sq_nonneg ((n%100/10 : ℕ):ℤ), mul_nonneg (by omega : 0 ≤ 9-((n%100%10 : ℕ):ℤ)) (by omega : 0 ≤ 9+((n%100%10 : ℕ):ℤ)),
    mul_nonneg (by omega : 0 ≤ 9-((n%100/10 : ℕ):ℤ)) (by omega : 0 ≤ 9+((n%100/10 : ℕ):ℤ))]

/-- Contract the interval to width twice the signed digit bound. -/
private theorem intervals (n : ℕ) : Good {x | x ≤ n} := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n ≤ 200
    · obtain ⟨k,hk⟩ := seed
      exact ⟨k, fun x hx => hk x (le_trans hx hs)⟩
    let b := 9*(n/100)+81
    have hshort : 2*b < n := by dsimp [b]; omega
    apply transfer 0 (n+1) (b:ℤ) _ (ih (2*b) hshort)
    intro x hx
    change x ≤ n at hx
    simp only [Nat.add_zero]
    have hp : n < 100^(n+1) := lt_trans (Nat.lt_succ_self n) (Nat.lt_pow_self (by decide : 1 < 100))
    obtain ⟨ha,hb⟩ := bound x
    refine ⟨lt_of_le_of_lt hx hp, ?_, ?_⟩
    · dsimp [b]; omega
    · change (D x + (b:ℤ)).toNat ≤ 2*b
      dsimp [b]; omega

end AlternatingDigitSquares

theorem OMA.solution : type_of% @OMA.S_oeis_a345680.main := by
  intro L
  obtain ⟨k,h⟩ := AlternatingDigitSquares.intervals L
  exact ⟨k, fun i hi => h i (Nat.le_of_lt hi)⟩

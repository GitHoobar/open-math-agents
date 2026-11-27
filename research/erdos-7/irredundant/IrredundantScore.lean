import ThirdOrderDeletion
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! Exact score of a complete bipartite coprimality graph with isolated
vertices, and the unbounded estimate for the dyadic construction. -/

namespace IrredundantScore

open Finset ThirdOrderDeletion
open scoped BigOperators

section Graph

variable {E K : Type*} [DecidableEq E] [DecidableEq K]

/-- Add mutually overlapping vertices with exactly the same coprime
neighbors inside the original family. No independent set uses two of them. -/
private theorem add_block (support : E → Finset K) (w : E → ℝ) (S X T : Finset E)
    (sub : T ⊆ S) (apart : Disjoint S X)
    (inside : ∀ x ∈ X, ∀ y ∈ X, ¬ Disjoint (support y) (support x))
    (neighbors : ∀ x ∈ X, ∀ y ∈ S, Disjoint (support y) (support x) ↔ y ∈ T) :
    signedQ support w (S ∪ X) = signedQ support w S - (∑ x ∈ X, w x) * signedQ support w T := by
  classical
  induction X using Finset.induction_on with
  | empty => simp
  | @insert x X hx ih =>
    have now := mem_insert_self x X
    have lift {y} (hy : y ∈ X) := mem_insert_of_mem hy (b := x)
    have all := ih (disjoint_of_subset_right (subset_insert x X) apart)
      (fun a ha b hb => inside a (lift ha) b (lift hb))
      (fun a ha => neighbors a (lift ha))
    have fresh : x ∉ S ∪ X := by
      intro h
      rcases mem_union.mp h with h | h
      · exact (disjoint_left.mp apart h) now
      · exact hx h
    obtain ⟨p, hp, _⟩ := not_disjoint_iff.mp (inside x now x now)
    let V := insert x (S ∪ X)
    have far_eq : far support V x = T := by
      ext y
      constructor
      · intro hy
        obtain ⟨hy, hd⟩ := mem_filter.mp hy
        rcases mem_insert.mp hy with rfl | hy
        · exact (inside y now y now hd).elim
        · rcases mem_union.mp hy with hy | hy
          · exact (neighbors x now y hy).mp hd
          · exact (inside x now y (lift hy) hd).elim
      · intro hy
        exact mem_filter.mpr ⟨mem_insert_of_mem (mem_union_left _ (sub hy)),
          (neighbors x now y (sub hy)).mpr hy⟩
    have erase : V.erase x = S ∪ X := erase_insert fresh
    have step := signedQ_deletion support w (mem_insert_self x (S ∪ X)) ⟨p, hp⟩
    change signedQ support w V = _ at step
    rw [show S ∪ insert x X = V by ext; simp [V], step, erase, far_eq, all, sum_insert hx]
    ring

/-- Full HKLT score for a complete bipartite coprimality graph on A and B,
with a further isolated block C. Every term of every order is included. -/
theorem bipartite_score (supp : E → Finset K) (w : E → ℝ) (A B C : Finset E)
    (ab : Disjoint A B) (bc : Disjoint (A ∪ B) C)
    (aa : ∀ x ∈ A, ∀ y ∈ A, ¬ Disjoint (supp y) (supp x))
    (bb : ∀ x ∈ B, ∀ y ∈ B, ¬ Disjoint (supp y) (supp x))
    (cc : ∀ x ∈ C, ∀ y ∈ C, ¬ Disjoint (supp y) (supp x))
    (cross : ∀ x ∈ B, ∀ y ∈ A, Disjoint (supp y) (supp x))
    (isolated : ∀ x ∈ C, ∀ y ∈ A∪B, ¬ Disjoint (supp y) (supp x)) :
    1 - signedQ supp w (A∪B∪C) =
      (∑ x ∈ A, w x) + (∑ x ∈ B, w x) + (∑ x ∈ C, w x) -
        (∑ x ∈ A, w x) * ∑ x ∈ B, w x := by
  have a := add_block supp w ∅ A ∅ (fun _ h => h) (by simp) aa (by simp)
  have b := add_block supp w A B A (fun _ h => h) ab bb (fun x hx y hy => iff_of_true (cross x hx y hy) hy)
  have c := add_block supp w (A ∪ B) C ∅ (empty_subset _) bc cc (fun x hx y hy => by simp [isolated x hx y hy])
  simp only [empty_union, signedQ_empty, mul_one] at a c
  rw [c, b, a]
  ring

end Graph

noncomputable def primeMass (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1 / (3 * (p : ℝ))

/-- The moduli 3p alone give arbitrarily large singleton mass even if all
primes at most five are forbidden. The primes form a finset, hence are distinct. -/
theorem arbitrarily_large_prime_mass (T : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ 5 < p) ∧ T < primeMass P := by
  classical
  obtain ⟨U, hu⟩ : ∃ U : Finset Nat.Primes, 3*T+6 < ∑ p ∈ U, 1/(p : ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  let f : Nat.Primes ↪ ℕ := Function.Embedding.subtype _
  let V := U.map f
  let P := V.filter (fun p => 5 < p)
  let S := V.filter (fun p => ¬ 5 < p)
  have isprime {p} (hp : p ∈ V) : Nat.Prime p := by
    obtain ⟨q, _, rfl⟩ := mem_map.mp hp
    exact q.2
  have hS : S.card ≤ 6 := by
    calc
      _ ≤ (range 6).card := card_le_card (by
        intro p hp
        have h := (mem_filter.mp hp).2
        exact mem_range.mpr (by omega))
      _ = _ := card_range _
  have small : (∑ p ∈ S, 1/(p : ℝ)) ≤ 6 := by
    calc
      _ ≤ ∑ _p ∈ S, (1 : ℝ) := by
        apply sum_le_sum
        intro p hp
        have h : (1 : ℝ) ≤ p := by exact_mod_cast (isprime (mem_filter.mp hp).1).one_le
        exact (div_le_one (by linarith)).mpr h
      _ = (S.card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast hS
  have all : 3*T+6 < ∑ p ∈ V, 1/(p : ℝ) := by
    dsimp only [V]
    rw [sum_map]
    exact hu
  have split : (∑ p ∈ P, 1/(p : ℝ)) + (∑ p ∈ S, 1/(p : ℝ)) = ∑ p ∈ V, 1/(p : ℝ) :=
    sum_filter_add_sum_filter_not _ _ _
  refine ⟨P, fun p hp => ⟨isprime (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩, ?_⟩
  have three : 3 * primeMass P = ∑ p ∈ P, 1/(p : ℝ) := by
    unfold primeMass
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    rw [mul_comm (3 : ℝ) (p : ℝ), div_mul_eq_div_div]
    ring
  linarith only [three, split, small, all]

noncomputable def a (h : ℕ) : ℝ := 19/16 - (1/2 : ℝ)^h
noncomputable def c (h N : ℕ) : ℝ := (1-(1/2 : ℝ)^h)/(5*N)
noncomputable def scoreFormula (P : Finset ℕ) (h N : ℕ) : ℝ :=
  a h + primeMass P + c h N - a h * primeMass P

theorem geometric (h : ℕ) : (∑ i ∈ range h, (1/2 : ℝ)^(i+1)) = 1-(1/2 : ℝ)^h := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_range_succ, ih, pow_succ]; ring

theorem mass_a (h : ℕ) :
    (∑ i ∈ range h, (1/2 : ℝ)^(i+1)) + (∑ i ∈ range 4, (1/2 : ℝ)^(i+1)/5) = a h := by
  rw [geometric, ← sum_div, geometric]
  unfold a
  ring

theorem mass_c (h N : ℕ) : (∑ i ∈ range h, (1/2 : ℝ)^(i+1)/(5*N)) = c h N := by
  rw [← sum_div, geometric, c]

theorem score_upper (P : Finset ℕ) (h N : ℕ) (hh : 4 ≤ h) (hN : 0 < N) :
    scoreFormula P h N ≤ 111/80 - primeMass P/8 := by
  have dy : (1/2 : ℝ)^h ≤ 1/16 := by
    calc
      _ ≤ (1/2 : ℝ)^4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hh
      _ = _ := by norm_num
  have dy0 : 0 ≤ (1/2 : ℝ)^h := by positivity
  have ha : 9/8 ≤ a h := by unfold a; linarith
  have hb : 0 ≤ primeMass P := sum_nonneg fun p _ => by positivity
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : c h N ≤ 1/5 := by
    unfold c
    apply (div_le_iff₀ (show (0 : ℝ)<5*N by positivity)).mpr
    linarith
  unfold scoreFormula
  have ha' : a h ≤ 19/16 := by unfold a; linarith
  linarith only [ha', hc, mul_le_mul_of_nonneg_right ha hb]

/-- One finite prime set works for every allowable number of holes and period. -/
theorem unbounded_below (target : ℝ) :
    ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p ∧ 5 < p) ∧
      ∀ h N : ℕ, 4 ≤ h → 0 < N → scoreFormula P h N < target := by
  obtain ⟨P, hp, mass⟩ := arbitrarily_large_prime_mass (max 0 (8*(111/80-target)))
  have pos : 0 < primeMass P := (le_max_left _ _).trans_lt mass
  have ne : P.Nonempty := by
    by_contra! empty
    simp [empty, primeMass] at pos
  refine ⟨P, ne, hp, fun h N hh hN => ?_⟩
  linarith only [(le_max_right _ _).trans_lt mass, score_upper P h N hh hN]

def layer (m h : ℕ) : Finset ℕ := (range h).image (fun i => m*2^(i+1))
def old (P : Finset ℕ) : Finset ℕ := P.image (fun p => 3*p)
def moduli (P : Finset ℕ) (h N : ℕ) : Finset ℕ :=
  layer 1 h ∪ layer 5 4 ∪ old P ∪ layer (5*N) h
noncomputable def hklt (V : Finset ℕ) : ℝ :=
  1 - signedQ Nat.primeFactors (fun n => 1/(n:ℝ)) V

theorem layer_injective {m : ℕ} (hm : 0 < m) : Function.Injective (fun i : ℕ => m*2^(i+1)) := by
  intro i j eq
  exact Nat.add_right_cancel (Nat.pow_right_injective (by decide : 2 ≤ 2) (Nat.eq_of_mul_eq_mul_left hm eq))

private theorem layer_mass (m h : ℕ) (hm : 0 < m) :
    (∑ d ∈ layer m h, 1/(d:ℝ)) = (1-(1/2:ℝ)^h)/m := by
  rw [layer, sum_image (layer_injective hm).injOn, ← geometric, sum_div]
  apply sum_congr rfl
  intro i _
  push_cast
  rw [div_pow, one_pow, div_div]
  ring

private theorem old_mass (P : Finset ℕ) : (∑ d ∈ old P, 1/(d:ℝ)) = primeMass P := by
  rw [old, sum_image]
  · simp [primeMass]
  · intro p _ q _ eq
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) eq

private theorem layer_two {m h d : ℕ} (hd : d ∈ layer m h) : 2 ∣ d := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hd
  rw [pow_succ]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

private theorem layer_pos {m h d : ℕ} (hm : 0 < m) (hd : d ∈ layer m h) : 0 < d := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hd
  positivity

private theorem layer_div {m h d : ℕ} (hd : d ∈ layer m h) : m ∣ d := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hd
  exact dvd_mul_right _ _

private theorem coprime_layer {m h d n : ℕ} (hm : m.Coprime n) (ht : Nat.Coprime 2 n)
    (hd : d ∈ layer m h) : d.Coprime n := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hd
  exact Nat.coprime_mul_iff_left.mpr ⟨hm, ht.pow_left _⟩

private theorem card_le_two {s X Y : Finset ℕ} (sub : s ⊆ X ∪ Y)
    (ind : Independent Nat.primeFactors s)
    (xx : ∀ u ∈ X, ∀ v ∈ X, ¬Disjoint u.primeFactors v.primeFactors)
    (yy : ∀ u ∈ Y, ∀ v ∈ Y, ¬Disjoint u.primeFactors v.primeFactors) : s.card ≤ 2 := by
  have small (Z : Finset ℕ) (zz : ∀ u ∈ Z, ∀ v ∈ Z, ¬Disjoint u.primeFactors v.primeFactors) :
      (s ∩ Z).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    exact zz u (mem_inter.mp hu).2 v (mem_inter.mp hv).2 (ind (mem_inter.mp hu).1 (mem_inter.mp hv).1 ne)
  have inc : s ⊆ (s∩X) ∪ (s∩Y) := by
    intro x hx
    rcases mem_union.mp (sub hx) with h | h
    · exact mem_union_left _ (mem_inter.mpr ⟨hx,h⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hx,h⟩)
  exact (card_le_card inc).trans ((card_union_le _ _).trans (Nat.add_le_add (small X xx) (small Y yy)))

private theorem concrete_data (P : Finset ℕ) (h N : ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p ∧ 5 < p) (hN : 0 < N) (three : 3 ∣ N) :
    Disjoint (layer 1 h) (layer 5 4) ∧ Disjoint (layer 1 h ∪ layer 5 4) (old P) ∧
    Disjoint (layer 1 h ∪ layer 5 4 ∪ old P) (layer (5*N) h) ∧
    (∀ S ⊆ moduli P h N, Independent Nat.primeFactors S → S.card ≤ 2) ∧
    hklt (moduli P h N) = scoreFormula P h N := by
  let A := layer 1 h ∪ layer 5 4
  let B := old P
  let C := layer (5*N) h
  have a2 {d} (hd : d ∈ A) : 2 ∣ d := (mem_union.mp hd).elim layer_two layer_two
  have apos {d} (hd : d ∈ A) : 0 < d :=
    (mem_union.mp hd).elim (layer_pos (by decide)) (layer_pos (by decide))
  have a3 {d} (hd : d ∈ A) : d.Coprime 3 :=
    (mem_union.mp hd).elim (coprime_layer (by decide) (by decide))
      (coprime_layer (by decide) (by decide))
  have bdata {d} (hd : d ∈ B) :
      0 < d ∧ 3 ∣ d ∧ Nat.Coprime 2 d ∧ Nat.Coprime 5 d := by
    obtain ⟨p, hP, rfl⟩ := mem_image.mp hd
    obtain ⟨pr, large⟩ := hp p hP
    refine ⟨by positivity, dvd_mul_right _ _, ?_, ?_⟩
    · exact Nat.coprime_mul_iff_right.mpr ⟨by decide, (Nat.coprime_primes (by decide) pr).mpr (by omega)⟩
    · exact Nat.coprime_mul_iff_right.mpr ⟨by decide, (Nat.coprime_primes (by decide) pr).mpr (by omega)⟩
  have cpos {d} (hd : d ∈ C) : 0 < d := layer_pos (by positivity : 0 < 5*N) hd
  have c3 {d} (hd : d ∈ C) : 3 ∣ d :=
    (three.trans (dvd_mul_left N 5)).trans (layer_div hd)
  have overlap {m u v : ℕ} (hm : 1 < m) (hu : 0 < u) (hv : 0 < v) (du : m ∣ u) (dv : m ∣ v) :
      ¬ Disjoint u.primeFactors v.primeFactors := fun h =>
    Nat.not_coprime_of_dvd_of_dvd hm du dv ((Nat.disjoint_primeFactors hu.ne' hv.ne').mp h)
  have ab : Disjoint A B := disjoint_left.mpr fun d ad bd =>
    ((by decide : Nat.Prime 2).dvd_iff_not_coprime.mp (a2 ad)) (bdata bd).2.2.1
  have bc : Disjoint (A∪B) C := by
    apply disjoint_left.mpr
    intro d hd cd
    rcases mem_union.mp hd with ad | bd
    · exact ((by decide : Nat.Prime 3).dvd_iff_not_coprime.mp (c3 cd)) (a3 ad).symm
    · exact ((by decide : Nat.Prime 2).dvd_iff_not_coprime.mp (layer_two cd)) (bdata bd).2.2.1
  have graph := bipartite_score Nat.primeFactors (fun d => 1/(d:ℝ)) A B C ab bc
    (fun x hx y hy => overlap (by decide : 1<2) (apos hy) (apos hx) (a2 hy) (a2 hx))
    (fun x hx y hy => overlap (by decide : 1<3) (bdata hy).1 (bdata hx).1 (bdata hy).2.1 (bdata hx).2.1)
    (fun x hx y hy => overlap (by decide : 1<2) (cpos hy) (cpos hx) (layer_two hy) (layer_two hx))
    (fun x hx y hy => ((mem_union.mp hy).elim
      (coprime_layer (Nat.coprime_one_left _) (bdata hx).2.2.1)
      (coprime_layer (bdata hx).2.2.2 (bdata hx).2.2.1)).disjoint_primeFactors)
    (fun x hx y hy => (mem_union.mp hy).elim
      (fun h => overlap (by decide : 1<2) (apos h) (cpos hx) (a2 h) (layer_two hx))
      (fun h => overlap (by decide : 1<3) (bdata h).1 (cpos hx) (bdata h).2.1 (c3 hx)))
  have layers : Disjoint (layer 1 h) (layer 5 4) := by
    apply disjoint_left.mpr
    intro d hd1 hd5
    exact ((by decide : Nat.Prime 5).dvd_iff_not_coprime.mp (layer_div hd5))
      (coprime_layer (by decide) (by decide) hd1).symm
  have a_mass : (∑ d ∈ A, 1/(d:ℝ)) = a h := by
    dsimp only [A]
    rw [sum_union layers, layer_mass _ _ (by decide), layer_mass _ _ (by decide), a]
    norm_num
    ring
  have c_mass : (∑ d ∈ C, 1/(d:ℝ)) = c h N := by
    dsimp only [C]
    rw [layer_mass _ _ (by positivity), c]
    push_cast
    rfl
  have rank : ∀ S ⊆ moduli P h N, Independent Nat.primeFactors S → S.card ≤ 2 := by
    intro S sub ind
    have subset : S ⊆ (A∪C)∪B := by
      intro x hx
      have inside : x ∈ (A∪B)∪C := sub hx
      simp only [mem_union] at inside ⊢
      tauto
    have two {d} (hd : d ∈ A∪C) : 2 ∣ d := (mem_union.mp hd).elim a2 layer_two
    have pos {d} (hd : d ∈ A∪C) : 0 < d := (mem_union.mp hd).elim apos cpos
    exact card_le_two subset ind
      (fun u hu v hv => overlap (by decide : 1<2) (pos hu) (pos hv) (two hu) (two hv))
      (fun u hu v hv => overlap (by decide : 1<3) (bdata hu).1 (bdata hv).1 (bdata hu).2.1 (bdata hv).2.1)
  refine ⟨layers, ab, bc, rank, ?_⟩
  change 1 - signedQ _ _ (A∪B∪C) = _
  rw [graph, a_mass, old_mass, c_mass]
  rfl

theorem blocks_disjoint (P : Finset ℕ) (h N : ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p ∧ 5 < p) (hN : 0 < N) (three : 3 ∣ N) :
    Disjoint (layer 1 h) (layer 5 4) ∧ Disjoint (layer 1 h ∪ layer 5 4) (old P) ∧
    Disjoint (layer 1 h ∪ layer 5 4 ∪ old P) (layer (5*N) h) := by
  obtain ⟨a, b, c, _⟩ := concrete_data P h N hp hN three
  exact ⟨a, b, c⟩

/-- The score of the actual integer moduli, with all multiplicities handled by
finset images. Only positivity and divisibility of N by three are used here. -/
theorem concrete_score (P : Finset ℕ) (h N : ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p ∧ 5 < p) (hN : 0 < N) (three : 3 ∣ N) :
    hklt (moduli P h N) = scoreFormula P h N :=
  (concrete_data P h N hp hN three).2.2.2.2

theorem no_triples (P : Finset ℕ) (h N : ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p ∧ 5 < p) (hN : 0 < N) (three : 3 ∣ N) :
    ∀ S ⊆ moduli P h N, Independent Nat.primeFactors S → S.card ≤ 2 :=
  (concrete_data P h N hp hN three).2.2.2.1

end IrredundantScore

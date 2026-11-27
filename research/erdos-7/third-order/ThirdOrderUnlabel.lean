import ThirdOrderTail
import ThirdOrderDeletion
import Mathlib.Data.Fintype.CardEmbedding

/-! An injective tuple enumerates its image. Grouping by that image
converts the weighted ordered count into a factorial times the unordered count. -/

namespace ThirdOrderUnlabel

open Finset
open scoped BigOperators Classical

variable {E C : Type*} [Fintype E] [DecidableEq E]

private def enumerations {j : ℕ} (s : Finset E) (hs : s.card = j) :
    {f : Fin j ↪ E // univ.map f = s} ≃ (Fin j ↪ ↥s) where
  toFun f := f.1.codRestrict (↑s) (fun i => by
    exact (congrArg (fun u : Finset E => f.1 i ∈ u) f.2).mp (mem_map_of_mem f.1 (mem_univ i)))
  invFun g := by
    let f := g.trans (Function.Embedding.subtype (· ∈ s))
    refine ⟨f, eq_of_subset_of_card_le ?_ ?_⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := mem_map.mp hx
      exact (g i).2
    · simp [hs]
  left_inv _ := by ext i; rfl
  right_inv _ := by ext i; rfl

/-- Every finite set family admits exactly j! injective orderings per
member of size j. No sign or positivity condition on the weights is needed. -/
theorem factorial_mass (F : Finset (Finset E)) (w : E → ℝ) (j : ℕ) :
    (j.factorial : ℝ) * ThirdOrderTail.mass F w j =
      ∑ f : Fin j ↪ E, if univ.map f ∈ F then ∏ i, w (f i) else 0 := by
  classical
  let tuples := univ.filter (fun f : Fin j ↪ E => univ.map f ∈ F)
  have maps (f) (hf : f ∈ tuples) : univ.map f ∈ ThirdOrderTail.level F j :=
    mem_filter.mpr ⟨(mem_filter.mp hf).2, by simp⟩
  rw [← sum_filter]
  change _ = ∑ f ∈ tuples, ∏ i, w (f i)
  rw [← sum_fiberwise_of_maps_to maps]
  unfold ThirdOrderTail.mass
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  obtain ⟨member, size⟩ := mem_filter.mp hs
  have fiber : tuples.filter (fun f => univ.map f = s) =
      univ.filter (fun f : Fin j ↪ E => univ.map f = s) := by
    ext f
    simp only [tuples, mem_filter, mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨h ▸ member, h⟩⟩
  rw [fiber]
  have card : (univ.filter (fun f : Fin j ↪ E => univ.map f = s)).card = j.factorial := by
    rw [← Fintype.card_subtype, Fintype.card_congr (enumerations s size), Fintype.card_embedding_eq]
    simp [size, Nat.descFactorial_self]
  calc
    _ = ∑ _f ∈ univ.filter (fun f : Fin j ↪ E => univ.map f = s), ∏ v ∈ s, w v := by
      rw [sum_const, nsmul_eq_mul, card]
    _ = _ := by
      apply sum_congr rfl
      intro f hf
      rw [← (mem_filter.mp hf).2, prod_map]

/-- For disjoint-support matchings this is the sum over ordered injective
tuples in V whose supports are pairwise disjoint. -/
theorem factorial_matching_mass [DecidableEq C] (V : Finset E) (support : E → Finset C)
    (w : E → ℝ) (j : ℕ) :
    (j.factorial : ℝ) * ThirdOrderTail.mass
        (V.powerset.filter (ThirdOrderDeletion.Independent support)) w j =
      ∑ f : Fin j ↪ E, if (∀ i, f i ∈ V) ∧ Pairwise (fun i k => Disjoint
          (support (f i)) (support (f k))) then ∏ i, w (f i) else 0 := by
  classical
  rw [factorial_mass]
  apply sum_congr rfl
  intro f _
  have mem (i : Fin j) : f i ∈ univ.map f := mem_map_of_mem f (mem_univ i)
  have cond : univ.map f ∈ V.powerset.filter (ThirdOrderDeletion.Independent support) ↔
      (∀ i, f i ∈ V) ∧ Pairwise (fun i k => Disjoint (support (f i)) (support (f k))) := by
    rw [mem_filter, mem_powerset]
    constructor
    · rintro ⟨sub, ind⟩
      exact ⟨fun i => sub (mem i), fun i k h => ind (mem i) (mem k) (fun e => h (f.injective e))⟩
    · rintro ⟨sub, ind⟩
      constructor
      · intro v hv
        obtain ⟨i, _, rfl⟩ := mem_map.mp hv
        exact sub i
      · intro v hv u hu h
        obtain ⟨i, _, rfl⟩ := mem_map.mp hv
        obtain ⟨k, _, rfl⟩ := mem_map.mp hu
        exact ind (fun e => h (congrArg f e))
  exact if_congr cond rfl rfl

end ThirdOrderUnlabel

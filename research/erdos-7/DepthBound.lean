import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Sym.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! A finite-depth bound for transitions between multisets of active hole types.
Each active prefix is represented by the nonempty subset of holes it still
contains. This file concerns a homogeneous relation on these multiset states. -/

namespace DepthBound

/-- A directed execution can be shortened by removing closed portions. No symmetry,
acyclicity or transitivity is required of the individual steps. -/
theorem simple_execution {α : Type*} (step : α → α → Prop) {start finish : α}
    (reach : Relation.ReflTransGen step start finish) :
    ∃ states : List α, states.head? = some start ∧ states.getLast? = some finish ∧
      states.IsChain step ∧ states.Nodup := by
  classical
  induction reach with
  | refl => exact ⟨[start], by simp, by simp, by simp, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨l, hs, ht, chain, unique⟩ := ih
    by_cases member : c ∈ l
    · obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp member
      have split : l = (pre ++ [c]) ++ post := by simpa using he
      rw [split] at chain unique
      refine ⟨pre ++ [c], ?_, by simp, chain.left_of_append, unique.of_append_left⟩
      cases pre <;> simpa [he] using hs
    · refine ⟨l ++ [c], by simp [hs], by simp, ?_, ?_⟩
      · apply chain.append (by simp)
        simpa [ht] using hbc
      · simpa [← List.concat_eq_append] using List.Nodup.concat member unique

/-- An active node carries a nonempty subset of the h input holes. -/
abbrev HoleType (h : ℕ) := {s : Finset (Fin h) // s ≠ ∅}

/-- Several active prefixes can have the same hole type. -/
abbrev State (h T : ℕ) := {s : Multiset (HoleType h) // s.card ≤ T}

private theorem drop_padding {α : Type*} (k : ℕ) :
    (Multiset.replicate k (none : Option α)).filterMap id = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [Multiset.replicate_succ, ih]

/-- Pad an unordered list to exactly T entries, using a new symbol for each
unused position. Removing the padding recovers the complete multiset. -/
private def padded {α : Type*} (T : ℕ) :
    {s : Multiset α // s.card ≤ T} ↪ Sym (Option α) T where
  toFun s := ⟨s.val.map some + Multiset.replicate (T - s.val.card) none,
    by simp [Nat.add_sub_of_le s.property]⟩
  inj' := by
    intro x y same
    apply Subtype.ext
    have he := congrArg (fun v : Sym (Option α) T => v.val.filterMap id) same
    simpa [Multiset.filterMap_add, Multiset.filterMap_map, drop_padding] using he

theorem number_of_states (h T : ℕ) :
    Nat.card (State h T) ≤ (2^h + T - 1).choose T := by
  classical
  let _ := Fintype.ofInjective (padded (α := HoleType h) T) (padded T).injective
  rw [Nat.card_eq_fintype_card]
  apply (Fintype.card_le_of_embedding (padded (α := HoleType h) T)).trans
  rw [Sym.card_sym_eq_choose]
  have alltypes : Fintype.card (Option (HoleType h)) = 2^h := by
    rw [Fintype.card_option]
    change Fintype.card {s : Finset (Fin h) // ¬s = ∅} + 1 = _
    rw [Fintype.card_subtype_compl]
    simp
    have positive : 0 < (2 : ℕ)^h := by positivity
    omega
  rw [alltypes]

/-- If a target configuration can be reached through states with at most T
active prefixes, it can be reached in fewer than the displayed number of steps.
The returned list includes both endpoints, so its edge count is length minus one. -/
theorem bounded_execution (h T : ℕ) (step : State h T → State h T → Prop)
    {start finish : State h T} (reach : Relation.ReflTransGen step start finish) :
    ∃ states : List (State h T), states.head? = some start ∧ states.getLast? = some finish ∧
      states.IsChain step ∧ states.Nodup ∧ states.length - 1 < (2^h + T - 1).choose T := by
  classical
  obtain ⟨l, hs, ht, hl, hu⟩ := simple_execution step reach
  refine ⟨l, hs, ht, hl, hu, ?_⟩
  let _ := Fintype.ofInjective (padded (α := HoleType h) T) (padded T).injective
  have len := hu.length_le_card
  have bound := number_of_states h T
  rw [Nat.card_eq_fintype_card] at bound
  have pos : 0 < l.length := by cases l <;> simp_all
  omega

/-- Each active prefix has p children. If at most D children can disappear at
each step, a run that eventually empties stays below the nondecreasing threshold. -/
theorem active_prefix_bound (p D N : ℕ) (hp : 2 ≤ p) (hD : 0 < D) (c : ℕ → ℕ)
    (terminal : c N = 0) (layer : ∀ j < N, p * c j ≤ c (j+1) + D) :
    ∀ j ≤ N, c j ≤ (D-1)/(p-1) := by
  intro j hj
  apply (Nat.le_div_iff_mul_le (by omega : 0 < p-1)).mpr
  rw [Nat.mul_comm]
  by_contra! large
  have monotone_until_end : ∀ k, j+k ≤ N → c j ≤ c (j+k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have prev := ih (by omega)
      have enough : D ≤ (p-1) * c (j+k) :=
        le_trans (by omega : D ≤ (p-1) * c j) (Nat.mul_le_mul_left _ prev)
      have split : p * c (j+k) = (p-1) * c (j+k) + c (j+k) := by
        conv_lhs => rw [show p = (p-1)+1 by omega, Nat.add_mul, Nat.one_mul]
      have hstep := layer (j+k) (by omega)
      have next : c j ≤ c ((j+k)+1) := by omega
      simpa only [Nat.add_assoc] using next
  have halt := monotone_until_end (N-j) (by omega)
  rw [show j+(N-j) = N by omega, terminal] at halt
  have zero : c j = 0 := by omega
  simp [zero] at large

end DepthBound

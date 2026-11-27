import Mathlib

/-!
# Positivity under deletion of events

The complete family on a set of coordinates consists of all available events
whose supports are contained in those coordinates. The graph joins events whose
supports intersect. Its signed independence polynomial on all induced event
families is positive if it is positive on the complete coordinate families.
-/

namespace ThirdOrderDeletion

variable {E C : Type*} [DecidableEq E] [DecidableEq C]

def complete (events : Finset E) (support : E → Finset C) (coords : Finset C) : Finset E :=
  events.filter fun x => support x ⊆ coords

def far (support : E → Finset C) (family : Finset E) (x : E) : Finset E :=
  family.filter fun y => Disjoint (support y) (support x)

theorem far_subset_erase (support : E → Finset C) (family : Finset E) (x : E)
    (hne : (support x).Nonempty) : far support family x ⊆ family.erase x := by
  intro y hy
  obtain ⟨hyF, hd⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_erase.mpr ⟨?_, hyF⟩
  rintro rfl
  obtain ⟨p, hp⟩ := hne
  exact Finset.disjoint_left.mp hd hp hp

def Independent (support : E → Finset C) (s : Finset E) : Prop :=
  (s : Set E).Pairwise fun x y => Disjoint (support x) (support y)

noncomputable def signedTerm (support : E → Finset C) (w : E → ℝ) (s : Finset E) : ℝ := by
  classical
  exact if Independent support s then ∏ x ∈ s, -w x else 0

noncomputable def signedQ (support : E → Finset C) (w : E → ℝ) (F : Finset E) : ℝ :=
  ∑ s ∈ F.powerset, signedTerm support w s

omit [DecidableEq E] [DecidableEq C] in
@[simp] theorem signedQ_empty (support : E → Finset C) (w : E → ℝ) :
    signedQ support w ∅ = 1 := by simp [signedQ, signedTerm, Independent]

private theorem signedTerm_insert (support : E → Finset C) (w : E → ℝ)
    {x : E} {s : Finset E} (hx : x ∉ s) :
    signedTerm support w (insert x s) =
      (-w x) * (if ∀ y ∈ s, Disjoint (support y) (support x) then signedTerm support w s else 0) := by
  classical
  have hind : Independent support (insert x s) ↔
      Independent support s ∧ ∀ y ∈ s, Disjoint (support y) (support x) := by
    unfold Independent
    rw [Finset.coe_insert, Set.pairwise_insert_of_notMem (by exact hx)]
    exact and_congr_right' ⟨fun h y hy => (h y hy).2, fun h y hy => ⟨(h y hy).symm, h y hy⟩⟩
  by_cases h : ∀ y ∈ s, Disjoint (support y) (support x) <;>
    by_cases i : Independent support s <;> simp [signedTerm, hind, h, i, Finset.prod_insert hx]

/-- Splitting the powerset according to membership of `x` gives the
deletion identity for the actual signed sum of independent families. -/
theorem signedQ_deletion (support : E → Finset C) (w : E → ℝ) {F : Finset E} {x : E}
    (hx : x ∈ F) (hne : (support x).Nonempty) :
    signedQ support w F = signedQ support w (F.erase x) -
      w x * signedQ support w (far support F x) := by
  classical
  let B := F.erase x
  let allowed (s : Finset E) := ∀ y ∈ s, Disjoint (support y) (support x)
  have restricted : B.powerset.filter allowed = (far support F x).powerset := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hB, hA⟩ y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (hB hy)).2, hA y hy⟩
    · intro h
      exact ⟨h.trans (far_subset_erase support F x hne), fun _ hy => (Finset.mem_filter.mp (h hy)).2⟩
  calc
    signedQ support w F = signedQ support w B + ∑ s ∈ B.powerset, signedTerm support w (insert x s) := by
      unfold signedQ
      conv_lhs => rw [← Finset.insert_erase hx]
      exact Finset.sum_powerset_insert (Finset.notMem_erase x F) _
    _ = signedQ support w B + (-w x) *
        ∑ s ∈ B.powerset, (if allowed s then signedTerm support w s else 0) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      exact signedTerm_insert support w (fun hin => Finset.notMem_erase x F ((Finset.mem_powerset.mp hs) hin))
    _ = signedQ support w (F.erase x) - w x * signedQ support w (far support F x) := by
      rw [← Finset.sum_filter, restricted]
      simp [signedQ, B, sub_eq_add_neg]

/-- The signed independence polynomial is specified by its vertex deletion
identity. The weights can vanish. Only nonempty supports are used. -/
theorem positive_induced (events : Finset E) (support : E → Finset C)
    (w : E → ℝ) (Q : Finset E → ℝ)
    (nonempty : ∀ x ∈ events, (support x).Nonempty) (hw : ∀ x ∈ events, 0 ≤ w x)
    (deletion : ∀ F ⊆ events, ∀ x ∈ F,
      Q F = Q (F.erase x) - w x * Q (far support F x))
    (coords : Finset C)
    (positive : ∀ T ⊆ coords, 0 < Q (complete events support T)) :
    ∀ F ⊆ complete events support coords, 0 < Q F := by
  induction coords using Finset.strongInductionOn with
  | _ coords ih =>
    let A := complete events support coords
    have hA (x : E) (hx : x ∈ A) : x ∈ events ∧ support x ⊆ coords :=
      Finset.mem_filter.mp hx
    have descend (D : Finset E) : 0 < Q (A \ D) := by
      induction D using Finset.induction_on with
      | empty => simpa [A] using positive coords (fun _ h => h)
      | @insert x D hxD old =>
        have erased : A \ (insert x D) = (A \ D).erase x := by
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        rw [erased]
        by_cases hx : x ∈ A \ D
        · obtain ⟨hAe, hAc⟩ := hA x (Finset.mem_sdiff.mp hx).1
          obtain ⟨p, hp⟩ := nonempty x hAe
          have hF : A \ D ⊆ events := fun y hy => (hA y (Finset.mem_sdiff.mp hy).1).1
          have away : far support (A \ D) x ⊆ complete events support (coords.erase p) := by
            intro y hy
            obtain ⟨hyD, hd⟩ := Finset.mem_filter.mp hy
            obtain ⟨hye, hyc⟩ := hA y (Finset.mem_sdiff.mp hyD).1
            refine Finset.mem_filter.mpr ⟨hye, ?_⟩
            intro q hq
            refine Finset.mem_erase.mpr ⟨?_, hyc hq⟩
            rintro rfl
            exact Finset.disjoint_left.mp hd hq hp
          have nearpos := ih (coords.erase p) (Finset.erase_ssubset (hAc hp))
            (fun T hT => positive T (hT.trans (Finset.erase_subset p coords))) _ away
          have eqn := deletion _ hF x hx
          linarith only [eqn, old, mul_nonneg (hw x hAe) nearpos.le]
        · simpa [Finset.erase_eq_of_notMem hx] using old
    intro F hF
    have difference : A \ (A \ F) = F := by
      ext x
      simp only [Finset.mem_sdiff]
      exact ⟨fun h => by tauto, fun h => ⟨hF h, by tauto⟩⟩
    simpa only [difference] using descend (A \ F)

/-- Positivity for complete coordinate families suffices for every
induced signed independence polynomial. -/
theorem signedQ_positive_induced (events : Finset E) (support : E → Finset C)
    (w : E → ℝ) (nonempty : ∀ x ∈ events, (support x).Nonempty) (hw : ∀ x ∈ events, 0 ≤ w x)
    (coords : Finset C)
    (positive : ∀ T ⊆ coords, 0 < signedQ support w (complete events support T)) :
    ∀ F ⊆ complete events support coords, 0 < signedQ support w F :=
  positive_induced events support w _ nonempty hw
    (fun _ hF x hx => signedQ_deletion support w hx (nonempty x (hF hx))) coords positive

end ThirdOrderDeletion




import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic



















namespace ConnesRigidity

namespace FeedbackCounting


theorem exists_ne_zero_of_sum_fin_two_eq_one
    (f : Fin 2 → ZMod 2)
    (h : ∑ i, f i = 1) :
    ∃ i, f i ≠ 0 := by
  by_contra hzero
  push Not at hzero
  have : (∑ i, f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hzero i
  rw [this] at h
  norm_num at h



theorem half_support_of_sum_fin_two_eq_one
    {A : Type*} [Fintype A]
    (f : A → Fin 2 → ZMod 2)
    (h : ∀ a, ∑ i, f a i = 1) :
    Fintype.card A ≤
      ((Finset.univ : Finset (A × Fin 2)).filter
        (fun x ↦ f x.1 x.2 ≠ 0)).card := by
  classical
  let choice : A → Fin 2 :=
    fun a ↦ Classical.choose (exists_ne_zero_of_sum_fin_two_eq_one (f a) (h a))
  let support :=
    (Finset.univ : Finset (A × Fin 2)).filter
      (fun x ↦ f x.1 x.2 ≠ 0)
  let selected : A → ↥support := fun a ↦
    ⟨(a, choice a), by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Classical.choose_spec
        (exists_ne_zero_of_sum_fin_two_eq_one (f a) (h a))⟩
  have hselected : Function.Injective selected := by
    intro a b hab
    exact congrArg (fun x ↦ x.1.1) hab
  rw [← Fintype.card_coe support]
  exact Fintype.card_le_of_injective selected hselected



theorem two_mul_support_card_ge_of_odd_two_point_partition
    {X A : Type*} [Fintype X] [Finite A]
    (e : X ≃ A × Fin 2)
    (f : X → ZMod 2)
    (hodd : ∀ a, ∑ i, f (e.symm (a, i)) = 1) :
    Fintype.card X ≤
      2 * ((Finset.univ : Finset X).filter (fun x ↦ f x ≠ 0)).card := by
  classical
  letI := Fintype.ofFinite A
  let productSupport :=
    (Finset.univ : Finset (A × Fin 2)).filter
      (fun x ↦ f (e.symm x) ≠ 0)
  let support :=
    (Finset.univ : Finset X).filter (fun x ↦ f x ≠ 0)
  have hhalf : Fintype.card A ≤ productSupport.card :=
    half_support_of_sum_fin_two_eq_one
      (fun a i ↦ f (e.symm (a, i))) hodd
  let supportEquiv : ↥productSupport ≃ ↥support := {
    toFun := fun x ↦ ⟨e.symm x.1, by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      have hx := x.property
      simp only [productSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx⟩
    invFun := fun x ↦ ⟨e x.1, by
      simp only [productSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      have hx := x.property
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simpa only [e.symm_apply_apply] using hx⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact e.apply_symm_apply x.1
    right_inv := by
      intro x
      apply Subtype.ext
      exact e.symm_apply_apply x.1
  }
  have hsupport : productSupport.card = support.card := by
    rw [← Fintype.card_coe productSupport, ← Fintype.card_coe support]
    exact Fintype.card_congr supportEquiv
  have hcard : Fintype.card X = 2 * Fintype.card A := by
    calc
      Fintype.card X = Fintype.card (A × Fin 2) :=
        Fintype.card_congr e
      _ = 2 * Fintype.card A := by simp [Nat.mul_comm]
  rw [hcard, ← hsupport]
  omega




theorem exists_ne_zero_of_sum_fin_four_eq_one
    (f : Fin 4 → ZMod 2)
    (h : ∑ i, f i = 1) :
    ∃ i, f i ≠ 0 := by
  by_contra hzero
  push Not at hzero
  have : (∑ i, f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hzero i
  rw [this] at h
  norm_num at h



theorem quarter_support_of_four_point_fibers
    {A : Type*} [Fintype A]
    (p : A → Fin 4 → Prop)
    [DecidablePred fun x : A × Fin 4 ↦ p x.1 x.2]
    (hp : ∀ a, ∃ i, p a i) :
    Fintype.card A ≤
      ((Finset.univ : Finset (A × Fin 4)).filter
        (fun x ↦ p x.1 x.2)).card := by
  classical
  let choice : A → Fin 4 := fun a ↦ Classical.choose (hp a)
  let inject : A → A × Fin 4 := fun a ↦ (a, choice a)
  have hinject : Function.Injective inject := by
    intro a b hab
    exact congrArg Prod.fst hab
  let goodSubtype :=
    {x : A × Fin 4 // x ∈
      ((Finset.univ : Finset (A × Fin 4)).filter
        (fun y ↦ p y.1 y.2))}
  let selected : A → goodSubtype := fun a ↦
    ⟨inject a, by
      simp [inject, choice, Classical.choose_spec (hp a)]⟩
  have hselected : Function.Injective selected := by
    intro a b hab
    exact hinject (congrArg Subtype.val hab)
  let good :=
    ((Finset.univ : Finset (A × Fin 4)).filter
      (fun y ↦ p y.1 y.2))
  change Fintype.card A ≤ good.card
  rw [← Fintype.card_coe good]
  exact Fintype.card_le_of_injective selected hselected




theorem quarter_support_of_sum_fin_four_eq_one
    {A : Type*} [Fintype A]
    (f : A → Fin 4 → ZMod 2) :
    (∀ a, ∑ i, f a i = 1) →
      Fintype.card A ≤
        ((Finset.univ : Finset (A × Fin 4)).filter
          (fun x ↦ f x.1 x.2 ≠ 0)).card := by
  intro h
  apply quarter_support_of_four_point_fibers
    (p := fun a i ↦ f a i ≠ 0)
  intro a
  exact exists_ne_zero_of_sum_fin_four_eq_one (f a) (h a)





theorem four_mul_support_card_ge_of_odd_four_point_partition
    {X A : Type*} [Fintype X] [Finite A]
    (e : X ≃ A × Fin 4)
    (f : X → ZMod 2)
    (hodd : ∀ a, ∑ i, f (e.symm (a, i)) = 1) :
    Fintype.card X ≤
      4 * ((Finset.univ : Finset X).filter (fun x ↦ f x ≠ 0)).card := by
  classical
  letI := Fintype.ofFinite A
  let productSupport :=
    (Finset.univ : Finset (A × Fin 4)).filter
      (fun x ↦ f (e.symm x) ≠ 0)
  let support :=
    (Finset.univ : Finset X).filter (fun x ↦ f x ≠ 0)
  have hquarter : Fintype.card A ≤ productSupport.card := by
    exact quarter_support_of_sum_fin_four_eq_one
      (fun a i ↦ f (e.symm (a, i))) hodd
  let supportEquiv : ↥productSupport ≃ ↥support := {
    toFun := fun x ↦ ⟨e.symm x.1, by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      have hx := x.property
      simp only [productSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx⟩
    invFun := fun x ↦ ⟨e x.1, by
      simp only [productSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      have hx := x.property
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simpa only [e.symm_apply_apply] using hx⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact e.apply_symm_apply x.1
    right_inv := by
      intro x
      apply Subtype.ext
      exact e.symm_apply_apply x.1
  }
  have hsupport : productSupport.card = support.card := by
    rw [← Fintype.card_coe productSupport, ← Fintype.card_coe support]
    exact Fintype.card_congr supportEquiv
  have hcard : Fintype.card X = 4 * Fintype.card A := by
    calc
      Fintype.card X = Fintype.card (A × Fin 4) :=
        Fintype.card_congr e
      _ = 4 * Fintype.card A := by simp [Nat.mul_comm]
  rw [hcard, ← hsupport]
  omega







theorem three_twenty_eighths_survive
    {α : Type*} [DecidableEq α]
    (univ good primitive : Finset α)
    (hquarter : univ.card ≤ 4 * good.card)
    (hseventh : 7 * primitive.card < univ.card) :
    3 * univ.card <
      28 * (good \ primitive).card := by
  have hinter : (good ∩ primitive).card ≤ primitive.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpartition :
      good.card = (good \ primitive).card + (good ∩ primitive).card := by
    exact (Finset.card_sdiff_add_card_inter good primitive).symm
  omega



theorem exists_good_not_primitive
    {α : Type*}
    (univ good primitive : Finset α)
    (hquarter : univ.card ≤ 4 * good.card)
    (hseventh : 7 * primitive.card < univ.card) :
    ∃ x ∈ good, x ∉ primitive := by
  classical
  have hdensity :=
    three_twenty_eighths_survive univ good primitive hquarter hseventh
  have hcard : 0 < (good \ primitive).card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨x, (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩

end FeedbackCounting

end ConnesRigidity

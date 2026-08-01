
import ConnesRigidity.FeedbackBooleanQuadratic

namespace ConnesRigidity

namespace FeedbackBooleanPolynomial

open FeedbackBooleanQuadratic
open FeedbackCounting

variable {ι : Type*} [DecidableEq ι]

@[simp]
theorem two_eq_zero_zmod_two : (2 : ZMod 2) = 0 := by
  rfl

theorem eq_one_of_ne_zero_zmod_two
    (a : ZMod 2) (ha : a ≠ 0) :
    a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

theorem sum_zmod_two (f : ZMod 2 → ZMod 2) :
    (∑ x, f x) = f 0 + f 1 := by
  rw [← (ZMod.finEquiv 2).toEquiv.sum_comp f, Fin.sum_univ_two]
  rfl

theorem binarySquareSum_const
    (c : ZMod 2) (i j : ι) (x : ι → ZMod 2) :
    binarySquareSum (fun _ ↦ c) i j x = 0 := by
  simp [binarySquareSum]

theorem binarySquareSum_coordinate
    (k i j : ι) (hij : i ≠ j) (x : ι → ZMod 2) :
    binarySquareSum (fun y ↦ y k) i j x = 0 := by
  by_cases hki : k = i
  · subst k
    simp [binarySquareSum, hij]
  · by_cases hkj : k = j
    · subst k
      simp [binarySquareSum]
    · simp [binarySquareSum, hki, hkj]

theorem binarySquareSum_selected_product
    (i j : ι) (hij : i ≠ j) (x : ι → ZMod 2) :
    binarySquareSum (fun y ↦ y i * y j) i j x = 1 := by
  simp [binarySquareSum, hij, sum_zmod_two]

theorem binarySquareSum_other_product
    (k l i j : ι) (hij : i ≠ j)
    (hpair : ¬((k = i ∧ l = j) ∨ (k = j ∧ l = i)))
    (x : ι → ZMod 2) :
    binarySquareSum (fun y ↦ y k * y l) i j x = 0 := by
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · exact (hpair (Or.inl ⟨rfl, hlj⟩)).elim
    · by_cases hli : l = i
      · subst l
        simp [binarySquareSum, hij]
      · simp [binarySquareSum, hij, hlj, hli]
  · by_cases hkj : k = j
    · subst k
      by_cases hli : l = i
      · exact (hpair (Or.inr ⟨rfl, hli⟩)).elim
      · by_cases hlj : l = j
        · subst l
          simp [binarySquareSum]
        · simp [binarySquareSum, hli, hlj]
    · by_cases hli : l = i
      · subst l
        simp [binarySquareSum, hij, hki, hkj]
      · by_cases hlj : l = j
        · subst l
          simp [binarySquareSum, hki, hkj]
        · simp [binarySquareSum, hki, hkj, hli, hlj]

theorem binarySquareSum_add
    (f g : (ι → ZMod 2) → ZMod 2)
    (i j : ι) (x : ι → ZMod 2) :
    binarySquareSum (fun y ↦ f y + g y) i j x =
      binarySquareSum f i j x + binarySquareSum g i j x := by
  simp [binarySquareSum, Finset.sum_add_distrib]

theorem binarySquareSum_mul_left
    (c : ZMod 2) (f : (ι → ZMod 2) → ZMod 2)
    (i j : ι) (x : ι → ZMod 2) :
    binarySquareSum (fun y ↦ c * f y) i j x =
      c * binarySquareSum f i j x := by
  simp [binarySquareSum, Finset.mul_sum]

theorem binarySquareSum_fintype_sum
    {κ : Type*} [Fintype κ]
    (f : κ → (ι → ZMod 2) → ZMod 2)
    (i j : ι) (x : ι → ZMod 2) :
    binarySquareSum (fun y ↦ ∑ k, f k y) i j x =
      ∑ k, binarySquareSum (f k) i j x := by
  unfold binarySquareSum
  calc
    (∑ a, ∑ b, ∑ k, f k (Function.update (Function.update x i a) j b)) =
        ∑ a, ∑ k, ∑ b, f k (Function.update (Function.update x i a) j b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ a, ∑ b,
        f k (Function.update (Function.update x i a) j b) := by
          rw [Finset.sum_comm]

abbrev OneCoordinateBase (i : ι) :=
  {k : ι // k ≠ i} → ZMod 2

def cubeEquivOneCoordinate
    (i : ι) :
    (ι → ZMod 2) ≃ OneCoordinateBase i × Fin 2 where
  toFun x :=
    (fun k ↦ x k, (ZMod.finEquiv 2).symm (x i))
  invFun y k :=
    if h : k = i then
      (ZMod.finEquiv 2) y.2
    else
      y.1 ⟨k, h⟩
  left_inv x := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  right_inv y := by
    apply Prod.ext_iff.mpr
    constructor
    · funext k
      simp [k.property]
    · simp

def affineEval
    [Fintype ι]
    (constant : ZMod 2)
    (linear : ι → ZMod 2)
    (x : ι → ZMod 2) : ZMod 2 :=
  constant + ∑ k, linear k * x k

set_option linter.flexible false in

theorem sum_cubeEquivOneCoordinate_affineEval
    [Fintype ι]
    (constant : ZMod 2)
    (linear : ι → ZMod 2)
    (i : ι)
    (hi : linear i = 1)
    (x : OneCoordinateBase i) :
    (∑ b : Fin 2,
      affineEval constant linear
        ((cubeEquivOneCoordinate i).symm (x, b))) = 1 := by
  classical
  simp [affineEval, cubeEquivOneCoordinate, Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro k _ hki
    simp [hki]
    rw [← two_mul, two_eq_zero_zmod_two, zero_mul]
  · simp

theorem two_mul_support_card_ge_of_affine_linear_ne_zero
    [Fintype ι]
    (constant : ZMod 2)
    (linear : ι → ZMod 2)
    (i : ι)
    (hi : linear i ≠ 0) :
    Fintype.card (ι → ZMod 2) ≤
      2 * ((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ affineEval constant linear x ≠ 0)).card := by
  classical
  apply two_mul_support_card_ge_of_odd_two_point_partition
    (cubeEquivOneCoordinate i) (affineEval constant linear)
  intro x
  apply sum_cubeEquivOneCoordinate_affineEval
  exact eq_one_of_ne_zero_zmod_two _ hi

abbrev StrictPair (ι : Type*) [LT ι] :=
  {p : ι × ι // p.1 < p.2}

structure BinaryQuadraticPolynomial
    (ι : Type*) [Fintype ι] [LinearOrder ι] where
  constant : ZMod 2
  linear : ι → ZMod 2
  quadratic : StrictPair ι → ZMod 2

namespace BinaryQuadraticPolynomial

variable [Fintype ι] [LinearOrder ι]

def eval
    (P : BinaryQuadraticPolynomial ι)
    (x : ι → ZMod 2) : ZMod 2 :=
  P.constant +
    (∑ k, P.linear k * x k) +
    ∑ p, P.quadratic p * (x p.1.1 * x p.1.2)

theorem binarySquareSum_eval
    (P : BinaryQuadraticPolynomial ι)
    (p₀ : StrictPair ι)
    (x : ι → ZMod 2) :
    binarySquareSum P.eval p₀.1.1 p₀.1.2 x = P.quadratic p₀ := by
  classical
  change
    binarySquareSum
      (fun y ↦ P.constant +
        (∑ k, P.linear k * y k) +
        ∑ p, P.quadratic p * (y p.1.1 * y p.1.2))
      p₀.1.1 p₀.1.2 x = P.quadratic p₀
  rw [binarySquareSum_add, binarySquareSum_add,
    binarySquareSum_const, zero_add,
    binarySquareSum_fintype_sum]
  have hlinear :
      (∑ k,
        binarySquareSum
          (fun y ↦ P.linear k * y k) p₀.1.1 p₀.1.2 x) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [binarySquareSum_mul_left,
      binarySquareSum_coordinate k p₀.1.1 p₀.1.2
        (ne_of_lt p₀.property) x, mul_zero]
  rw [hlinear, zero_add, binarySquareSum_fintype_sum]
  rw [Finset.sum_eq_single p₀]
  · rw [binarySquareSum_mul_left,
      binarySquareSum_selected_product p₀.1.1 p₀.1.2
        (ne_of_lt p₀.property) x,
      mul_one]
  · intro p _ hp
    rw [binarySquareSum_mul_left]
    have hpair :
        ¬((p.1.1 = p₀.1.1 ∧ p.1.2 = p₀.1.2) ∨
          (p.1.1 = p₀.1.2 ∧ p.1.2 = p₀.1.1)) := by
      intro h
      rcases h with h | h
      · apply hp
        apply Subtype.ext
        exact Prod.ext h.1 h.2
      · have hp_lt : p₀.1.2 < p₀.1.1 := by simpa [h.1, h.2] using p.property
        exact (lt_asymm p₀.property hp_lt).elim
    rw [binarySquareSum_other_product
      p.1.1 p.1.2 p₀.1.1 p₀.1.2
      (ne_of_lt p₀.property) hpair x, mul_zero]
  · intro hp
    exact (hp (Finset.mem_univ p₀)).elim

omit [DecidableEq ι] in

theorem eval_eq_affine_of_quadratic_eq_zero
    (P : BinaryQuadraticPolynomial ι)
    (hq : ∀ p, P.quadratic p = 0) :
    P.eval = affineEval P.constant P.linear := by
  funext x
  simp [eval, affineEval, hq]

theorem four_mul_support_card_ge_of_quadratic_coeff_ne_zero
    (P : BinaryQuadraticPolynomial ι)
    (p₀ : StrictPair ι)
    (hp₀ : P.quadratic p₀ ≠ 0) :
    Fintype.card (ι → ZMod 2) ≤
      4 * ((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ P.eval x ≠ 0)).card := by
  apply four_mul_support_card_ge_of_binarySquareSum_eq_one
    P.eval p₀.1.1 p₀.1.2 (ne_of_lt p₀.property)
  intro x
  rw [P.binarySquareSum_eval p₀ x]
  exact eq_one_of_ne_zero_zmod_two _ hp₀

theorem three_twenty_eighths_nonprimitive_support_of_quadratic_coeff_ne_zero
    (P : BinaryQuadraticPolynomial ι)
    (p₀ : StrictPair ι)
    (hp₀ : P.quadratic p₀ ≠ 0)
    (primitive : Finset (ι → ZMod 2))
    (hprimitive :
      7 * primitive.card < Fintype.card (ι → ZMod 2)) :
    3 * Fintype.card (ι → ZMod 2) <
      28 * (((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ P.eval x ≠ 0)) \ primitive).card := by
  apply three_twenty_eighths_nonprimitive_support
    P.eval p₀.1.1 p₀.1.2 (ne_of_lt p₀.property)
  · intro x
    rw [P.binarySquareSum_eval p₀ x]
    exact eq_one_of_ne_zero_zmod_two _ hp₀
  · exact hprimitive

theorem exists_nonprimitive_of_quadratic_coeff_ne_zero
    (P : BinaryQuadraticPolynomial ι)
    (p₀ : StrictPair ι)
    (hp₀ : P.quadratic p₀ ≠ 0)
    (primitive : Finset (ι → ZMod 2))
    (hprimitive :
      7 * primitive.card < Fintype.card (ι → ZMod 2)) :
    ∃ x, P.eval x ≠ 0 ∧ x ∉ primitive := by
  apply exists_nonprimitive_of_binarySquareSum_eq_one
    P.eval p₀.1.1 p₀.1.2 (ne_of_lt p₀.property)
  · intro x
    rw [P.binarySquareSum_eval p₀ x]
    exact eq_one_of_ne_zero_zmod_two _ hp₀
  · exact hprimitive

theorem four_mul_support_card_ge_of_eval_nonzero
    (P : BinaryQuadraticPolynomial ι)
    (hP : ∃ x, P.eval x ≠ 0) :
    Fintype.card (ι → ZMod 2) ≤
      4 * ((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ P.eval x ≠ 0)).card := by
  classical
  by_cases hquadratic : ∃ p, P.quadratic p ≠ 0
  · obtain ⟨p, hp⟩ := hquadratic
    exact P.four_mul_support_card_ge_of_quadratic_coeff_ne_zero p hp
  · have hquadratic_zero : ∀ p, P.quadratic p = 0 := by
      intro p
      by_contra hp
      exact hquadratic ⟨p, hp⟩
    have heval : P.eval = affineEval P.constant P.linear :=
      P.eval_eq_affine_of_quadratic_eq_zero hquadratic_zero
    by_cases hlinear : ∃ i, P.linear i ≠ 0
    · obtain ⟨i, hi⟩ := hlinear
      have hhalf :=
        two_mul_support_card_ge_of_affine_linear_ne_zero
          P.constant P.linear i hi
      have hsupport :
          ((Finset.univ : Finset (ι → ZMod 2)).filter
            (fun x ↦ P.eval x ≠ 0)) =
          ((Finset.univ : Finset (ι → ZMod 2)).filter
            (fun x ↦ affineEval P.constant P.linear x ≠ 0)) := by
        ext x
        simp [heval]
      rw [hsupport]
      omega
    · have hlinear_zero : ∀ i, P.linear i = 0 := by
        intro i
        by_contra hi
        exact hlinear ⟨i, hi⟩
      obtain ⟨x, hx⟩ := hP
      have hconstant : P.constant ≠ 0 := by
        simpa [eval, hquadratic_zero, hlinear_zero] using hx
      have hsupport :
          ((Finset.univ : Finset (ι → ZMod 2)).filter
            (fun x ↦ P.eval x ≠ 0)) =
          Finset.univ := by
        ext y
        simp [eval, hquadratic_zero, hlinear_zero, hconstant]
      rw [hsupport, Finset.card_univ]
      omega

theorem three_twenty_eighths_nonprimitive_support_of_eval_nonzero
    (P : BinaryQuadraticPolynomial ι)
    (hP : ∃ x, P.eval x ≠ 0)
    (primitive : Finset (ι → ZMod 2))
    (hprimitive :
      7 * primitive.card < Fintype.card (ι → ZMod 2)) :
    3 * Fintype.card (ι → ZMod 2) <
      28 * (((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ P.eval x ≠ 0)) \ primitive).card := by
  apply three_twenty_eighths_survive
    (Finset.univ : Finset (ι → ZMod 2))
    ((Finset.univ : Finset (ι → ZMod 2)).filter
      (fun x ↦ P.eval x ≠ 0))
    primitive
  · simpa using P.four_mul_support_card_ge_of_eval_nonzero hP
  · simpa using hprimitive

theorem exists_nonprimitive_of_eval_nonzero
    (P : BinaryQuadraticPolynomial ι)
    (hP : ∃ x, P.eval x ≠ 0)
    (primitive : Finset (ι → ZMod 2))
    (hprimitive :
      7 * primitive.card < Fintype.card (ι → ZMod 2)) :
    ∃ x, P.eval x ≠ 0 ∧ x ∉ primitive := by
  classical
  let support :=
    (Finset.univ : Finset (ι → ZMod 2)).filter
      (fun x ↦ P.eval x ≠ 0)
  have hquarter :
      (Finset.univ : Finset (ι → ZMod 2)).card ≤
        4 * support.card := by
    simpa [support] using P.four_mul_support_card_ge_of_eval_nonzero hP
  obtain ⟨x, hxsupport, hxprimitive⟩ :=
    exists_good_not_primitive
      (Finset.univ : Finset (ι → ZMod 2))
      support primitive hquarter (by simpa using hprimitive)
  exact ⟨x, (Finset.mem_filter.mp hxsupport).2, hxprimitive⟩

end BinaryQuadraticPolynomial

end FeedbackBooleanPolynomial

end ConnesRigidity


import ConnesRigidity.FeedbackCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

namespace ConnesRigidity

namespace FeedbackBooleanQuadratic

open FeedbackCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def clearTwoCoordinates
    (i j : ι) (x : ι → ZMod 2) : ι → ZMod 2 :=
  Function.update (Function.update x i 0) j 0

abbrev TwoCoordinateBase (i j : ι) :=
  {x : ι → ZMod 2 // x i = 0 ∧ x j = 0}

def zmodTwoPairEquivFinFour :
    (ZMod 2 × ZMod 2) ≃ Fin 4 :=
  (Equiv.prodCongr (ZMod.finEquiv 2).symm.toEquiv
      (ZMod.finEquiv 2).symm.toEquiv).trans
    finProdFinEquiv

def cubeEquivTwoCoordinateBase
    (i j : ι) (hij : i ≠ j) :
    (ι → ZMod 2) ≃ TwoCoordinateBase i j × Fin 4 where
  toFun x :=
    (⟨clearTwoCoordinates i j x, by
      constructor
      · simp [clearTwoCoordinates, hij]
      · simp [clearTwoCoordinates]⟩,
      zmodTwoPairEquivFinFour (x i, x j))
  invFun y :=
    let bits := zmodTwoPairEquivFinFour.symm y.2
    Function.update (Function.update y.1.1 i bits.1) j bits.2
  left_inv x := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [clearTwoCoordinates, hij, zmodTwoPairEquivFinFour]
    · by_cases hkj : k = j
      · subst k
        simp [clearTwoCoordinates, zmodTwoPairEquivFinFour]
      · simp [clearTwoCoordinates, hki, hkj, zmodTwoPairEquivFinFour]
  right_inv y := by
    rcases y with ⟨x, k⟩
    apply Prod.ext_iff.mpr
    constructor
    · apply Subtype.ext
      funext r
      by_cases hri : r = i
      · subst r
        simp [clearTwoCoordinates, hij, zmodTwoPairEquivFinFour, x.property]
      · by_cases hrj : r = j
        · subst r
          simp [clearTwoCoordinates, zmodTwoPairEquivFinFour, x.property]
        · simp [clearTwoCoordinates, hri, hrj, zmodTwoPairEquivFinFour]
    · simp [hij, zmodTwoPairEquivFinFour]

def binarySquareSum
    (f : (ι → ZMod 2) → ZMod 2)
    (i j : ι) (x : ι → ZMod 2) : ZMod 2 :=
  ∑ a : ZMod 2, ∑ b : ZMod 2,
    f (Function.update (Function.update x i a) j b)

omit [Fintype ι] in

theorem sum_cubeEquivTwoCoordinateBase_fiber
    (f : (ι → ZMod 2) → ZMod 2)
    (i j : ι) (hij : i ≠ j)
    (x : TwoCoordinateBase i j) :
    (∑ k : Fin 4,
        f ((cubeEquivTwoCoordinateBase i j hij).symm (x, k))) =
      binarySquareSum f i j x.1 := by
  classical
  rw [binarySquareSum, ← Fintype.sum_prod_type']
  rw [← zmodTwoPairEquivFinFour.symm.sum_comp
    (fun p : ZMod 2 × ZMod 2 ↦
      f (Function.update (Function.update x.1 i p.1) j p.2))]
  apply Finset.sum_congr rfl
  intro k _
  rfl

theorem four_mul_support_card_ge_of_binarySquareSum_eq_one
    (f : (ι → ZMod 2) → ZMod 2)
    (i j : ι) (hij : i ≠ j)
    (hsecond : ∀ x, binarySquareSum f i j x = 1) :
    Fintype.card (ι → ZMod 2) ≤
      4 * ((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ f x ≠ 0)).card := by
  classical
  apply four_mul_support_card_ge_of_odd_four_point_partition
    (cubeEquivTwoCoordinateBase i j hij) f
  intro x
  rw [sum_cubeEquivTwoCoordinateBase_fiber]
  exact hsecond x.1

theorem three_twenty_eighths_nonprimitive_support
    (f : (ι → ZMod 2) → ZMod 2)
    (i j : ι) (hij : i ≠ j)
    (hsecond : ∀ x, binarySquareSum f i j x = 1)
    (primitive : Finset (ι → ZMod 2))
    (hprimitive :
      7 * primitive.card < Fintype.card (ι → ZMod 2)) :
    3 * Fintype.card (ι → ZMod 2) <
      28 * (((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ f x ≠ 0)) \ primitive).card := by
  classical
  have hquarter :=
    four_mul_support_card_ge_of_binarySquareSum_eq_one
      f i j hij hsecond
  have hdensity :=
    three_twenty_eighths_survive
      (Finset.univ : Finset (ι → ZMod 2))
      ((Finset.univ : Finset (ι → ZMod 2)).filter
        (fun x ↦ f x ≠ 0))
      primitive
      (by simpa using hquarter)
      (by simpa using hprimitive)
  simpa using hdensity

theorem exists_nonprimitive_of_binarySquareSum_eq_one
    (f : (ι → ZMod 2) → ZMod 2)
    (i j : ι) (hij : i ≠ j)
    (hsecond : ∀ x, binarySquareSum f i j x = 1)
    (primitive : Finset (ι → ZMod 2))
    (hprimitive :
      7 * primitive.card < Fintype.card (ι → ZMod 2)) :
    ∃ x, f x ≠ 0 ∧ x ∉ primitive := by
  classical
  let support :=
    (Finset.univ : Finset (ι → ZMod 2)).filter (fun x ↦ f x ≠ 0)
  have hquarter :
      (Finset.univ : Finset (ι → ZMod 2)).card ≤ 4 * support.card := by
    simpa [support] using
      four_mul_support_card_ge_of_binarySquareSum_eq_one
        f i j hij hsecond
  obtain ⟨x, hxsupport, hxprimitive⟩ :=
    exists_good_not_primitive
      (Finset.univ : Finset (ι → ZMod 2))
      support primitive hquarter (by simpa using hprimitive)
  exact ⟨x, (Finset.mem_filter.mp hxsupport).2, hxprimitive⟩

end FeedbackBooleanQuadratic

end ConnesRigidity

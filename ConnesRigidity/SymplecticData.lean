
import ConnesRigidity.LiftedCocycle
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.SymplecticGroup

namespace ConnesRigidity

open Matrix

abbrev SymplecticIndex := Fin 2 ⊕ Fin 2

abbrev IntegralLattice := SymplecticIndex → ℤ

abbrev ModTwoSpace := SymplecticIndex → ZMod 2

abbrev IntegralSymplecticGroup := Matrix.symplecticGroup (Fin 2) ℤ

instance : Countable IntegralSymplecticGroup := by
  let f : IntegralSymplecticGroup → SymplecticIndex → SymplecticIndex → ℤ :=
    fun g i j ↦ g.1 i j
  apply (show Function.Injective f by
    intro g h hgh
    apply Subtype.ext
    funext i j
    exact congr_fun (congr_fun hgh i) j).countable

instance : DistribMulAction IntegralSymplecticGroup IntegralLattice :=
  DistribMulAction.compHom IntegralLattice
    (Matrix.symplecticGroup (Fin 2) ℤ).subtype

def reducedMatrixHom :
    IntegralSymplecticGroup →* Matrix SymplecticIndex SymplecticIndex (ZMod 2) where
  toFun g := (g.1 : Matrix SymplecticIndex SymplecticIndex ℤ).map
    (Int.castRingHom (ZMod 2))
  map_one' :=
    Matrix.map_one (Int.castRingHom (ZMod 2)) (map_zero _) (map_one _)
  map_mul' g h := by
    ext i j
    simp [Matrix.mul_apply]

instance : DistribMulAction IntegralSymplecticGroup ModTwoSpace :=
  DistribMulAction.compHom ModTwoSpace reducedMatrixHom

def reduceVector : IntegralLattice →+ ModTwoSpace where
  toFun v i := (v i : ZMod 2)
  map_zero' := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp

@[simp]
theorem reduceVector_apply (v : IntegralLattice) (i : SymplecticIndex) :
    reduceVector v i = (v i : ZMod 2) := rfl

def liftVector (w : ModTwoSpace) : IntegralLattice :=
  fun i ↦ ZMod.cast (w i)

@[simp]
theorem reduceVector_liftVector (w : ModTwoSpace) :
    reduceVector (liftVector w) = w := by
  funext i
  change ((ZMod.cast (w i) : ℤ) : ZMod 2) = w i
  exact ZMod.intCast_zmod_cast _

@[simp]
theorem liftVector_zero : liftVector (0 : ModTwoSpace) = 0 := by
  funext i
  simp [liftVector]

theorem reduceVector_smul (g : IntegralSymplecticGroup) (v : IntegralLattice) :
    reduceVector (g • v) = g • reduceVector v := by
  funext i
  exact RingHom.map_mulVec (Int.castRingHom (ZMod 2)) g.1 v i

theorem modTwoSpace_exponent_two (w : ModTwoSpace) :
    (2 : ℕ) • w = 0 := by
  funext i
  change (2 : ℕ) • w i = 0
  rw [two_nsmul]
  exact CharTwo.add_self_eq_zero _

theorem exists_half_of_reduceVector_eq_zero
    (v : IntegralLattice) (hv : reduceVector v = 0) :
    ∃ u : IntegralLattice, (2 : ℕ) • u = v := by
  have hdiv : ∀ i, (2 : ℤ) ∣ v i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) 2).mp
    have hi := congr_fun hv i
    simpa using hi
  choose u hu using hdiv
  refine ⟨u, ?_⟩
  funext i
  change (2 : ℕ) • u i = v i
  simpa [nsmul_eq_mul] using (hu i).symm

theorem two_nsmul_integralLattice_injective :
    Function.Injective (fun v : IntegralLattice ↦ (2 : ℕ) • v) := by
  exact nsmul_right_injective (by norm_num : (2 : ℕ) ≠ 0)

def symplecticModTwoLiftingData :
    ModTwoLiftingData IntegralSymplecticGroup IntegralLattice ModTwoSpace where
  reduce := reduceVector
  reduce_smul := reduceVector_smul
  lift := liftVector
  reduce_lift := reduceVector_liftVector
  lift_zero := liftVector_zero
  exponent_two := modTwoSpace_exponent_two
  exists_half_of_reduce_eq_zero := exists_half_of_reduceVector_eq_zero
  two_nsmul_injective := two_nsmul_integralLattice_injective

def modTwoSymplecticForm (x y : ModTwoSpace) : ZMod 2 :=
  ∑ i : Fin 2, (x (Sum.inl i) * y (Sum.inr i) +
    x (Sum.inr i) * y (Sum.inl i))

def standardQuadraticForm (x : ModTwoSpace) : ZMod 2 :=
  ∑ i : Fin 2, x (Sum.inl i) * x (Sum.inr i)

theorem standardQuadraticForm_add (x y : ModTwoSpace) :
    standardQuadraticForm (x + y) =
      standardQuadraticForm x + standardQuadraticForm y + modTwoSymplecticForm x y := by
  classical
  simp only [standardQuadraticForm, modTwoSymplecticForm, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  have hcross :
      (∑ i : Fin 2, y (Sum.inl i) * x (Sum.inr i)) =
        ∑ i : Fin 2, x (Sum.inr i) * y (Sum.inl i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hcross]
  abel

structure IntegralSymplecticCocycleInput where
  d : IntegralSymplecticGroup → ModTwoSpace
  defining_identity :
    ∀ (g : IntegralSymplecticGroup) (w : ModTwoSpace),
      standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w =
        modTwoSymplecticForm (d g) w
  cocycle : groupCohomology.IsCocycle₁ d
  not_coboundary : ¬groupCohomology.IsCoboundary₁ d
  integral_one_cocycles_are_coboundaries :
    ∀ F : IntegralSymplecticGroup → IntegralLattice,
      groupCohomology.IsCocycle₁ F → groupCohomology.IsCoboundary₁ F

namespace IntegralSymplecticCocycleInput

variable (I : IntegralSymplecticCocycleInput)

noncomputable def twoCocycle :
    NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice :=
  symplecticModTwoLiftingData.liftedTwoCocycle I.d I.cocycle

theorem twoCocycle_not_isCoboundary :
    ¬I.twoCocycle.IsCoboundary :=
  symplecticModTwoLiftingData.liftedTwoCocycle_not_isCoboundary
    I.d I.cocycle I.not_coboundary I.integral_one_cocycles_are_coboundaries

abbrev GammaZero :=
  CocycleExtension
    (NormalizedAddCocycle.zero :
      NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)

noncomputable abbrev GammaOne :=
  CocycleExtension I.twoCocycle

theorem gammaOne_has_no_splitting :
    IsEmpty (CocycleExtension.Splitting I.twoCocycle) :=
  CocycleExtension.noSplitting_of_not_isCoboundary I.twoCocycle
    I.twoCocycle_not_isCoboundary

end IntegralSymplecticCocycleInput

end ConnesRigidity


import ConnesRigidity.SymplecticData

namespace ConnesRigidity

open Matrix

abbrev ModTwoSymplecticGroup :=
  Matrix.symplecticGroup (Fin 2) (ZMod 2)

instance modTwoSymplecticGroupDecidableMem : DecidablePred
    (fun A : Matrix SymplecticIndex SymplecticIndex (ZMod 2) =>
      A ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2)) :=
  fun A => decidable_of_iff
    (A * Matrix.J (Fin 2) (ZMod 2) * Matrix.transpose A =
      Matrix.J (Fin 2) (ZMod 2))
    (SymplecticGroup.mem_iff).symm

instance : Fintype ModTwoSymplecticGroup :=
  Subtype.fintype _

def reducedSymplecticHom :
    IntegralSymplecticGroup →* ModTwoSymplecticGroup where
  toFun g :=
    ⟨(g.1 : Matrix SymplecticIndex SymplecticIndex ℤ).map
        (Int.castRingHom (ZMod 2)),
      SymplecticGroup.map_mem g.2 (Int.castRingHom (ZMod 2))⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one (Int.castRingHom (ZMod 2)) (map_zero _) (map_one _)
  map_mul' g h := by
    apply Subtype.ext
    ext i j
    simp [Matrix.mul_apply]

@[simp]
theorem reducedSymplecticHom_coe (g : IntegralSymplecticGroup) :
    (reducedSymplecticHom g : Matrix SymplecticIndex SymplecticIndex (ZMod 2)) =
      reducedMatrixHom g :=
  rfl

instance : DistribMulAction ModTwoSymplecticGroup ModTwoSpace :=
  DistribMulAction.compHom ModTwoSpace
    (Matrix.symplecticGroup (Fin 2) (ZMod 2)).subtype

def modTwoBasis (i : SymplecticIndex) : ModTwoSpace :=
  Pi.single i 1

def finiteQuadraticCocycle (g : ModTwoSymplecticGroup) : ModTwoSpace
  | Sum.inl i =>
      standardQuadraticForm (g⁻¹ • modTwoBasis (Sum.inr i)) +
        standardQuadraticForm (modTwoBasis (Sum.inr i))
  | Sum.inr i =>
      standardQuadraticForm (g⁻¹ • modTwoBasis (Sum.inl i)) +
        standardQuadraticForm (modTwoBasis (Sum.inl i))

theorem modTwoSymplecticForm_eq_dotProduct (x y : ModTwoSpace) :
    modTwoSymplecticForm x y =
      dotProduct x ((Matrix.J (Fin 2) (ZMod 2)).mulVec y) := by
  simp [modTwoSymplecticForm, Matrix.J, Matrix.mulVec, dotProduct]
  abel

theorem modTwoSymplecticForm_smul
    (g : ModTwoSymplecticGroup) (x y : ModTwoSpace) :
    modTwoSymplecticForm (g • x) (g • y) = modTwoSymplecticForm x y := by
  rw [modTwoSymplecticForm_eq_dotProduct, modTwoSymplecticForm_eq_dotProduct]
  change dotProduct (g.1.mulVec x)
      ((Matrix.J (Fin 2) (ZMod 2)).mulVec (g.1.mulVec y)) =
    dotProduct x ((Matrix.J (Fin 2) (ZMod 2)).mulVec y)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [SymplecticGroup.mem_iff'.mp g.2]
  rw [← Matrix.dotProduct_mulVec]

theorem modTwoSymplecticForm_add_right (x y z : ModTwoSpace) :
    modTwoSymplecticForm x (y + z) =
      modTwoSymplecticForm x y + modTwoSymplecticForm x z := by
  simp [modTwoSymplecticForm, mul_add, Finset.sum_add_distrib]
  abel

def quadraticDefectLinear (g : ModTwoSymplecticGroup) :
    ModTwoSpace →ₗ[ZMod 2] ZMod 2 where
  toFun w := standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w
  map_add' x y := by
    change
      standardQuadraticForm ((g⁻¹).1.mulVec (x + y)) +
          standardQuadraticForm (x + y) =
        standardQuadraticForm ((g⁻¹).1.mulVec x) + standardQuadraticForm x +
          (standardQuadraticForm ((g⁻¹).1.mulVec y) + standardQuadraticForm y)
    rw [Matrix.mulVec_add, standardQuadraticForm_add, standardQuadraticForm_add]
    have hinv := modTwoSymplecticForm_smul g⁻¹ x y
    change modTwoSymplecticForm ((g⁻¹).1.mulVec x) ((g⁻¹).1.mulVec y) =
      modTwoSymplecticForm x y at hinv
    rw [hinv]
    have hcancel :
        modTwoSymplecticForm x y + modTwoSymplecticForm x y = 0 :=
      CharTwo.add_self_eq_zero _
    calc
      standardQuadraticForm ((g⁻¹).1.mulVec x) +
            standardQuadraticForm ((g⁻¹).1.mulVec y) +
            modTwoSymplecticForm x y +
          (standardQuadraticForm x + standardQuadraticForm y +
            modTwoSymplecticForm x y) =
          (standardQuadraticForm ((g⁻¹).1.mulVec x) + standardQuadraticForm x) +
            (standardQuadraticForm ((g⁻¹).1.mulVec y) + standardQuadraticForm y) +
              (modTwoSymplecticForm x y + modTwoSymplecticForm x y) := by abel
      _ = _ := by rw [hcancel]; simp
  map_smul' c x := by
    change
      standardQuadraticForm ((g⁻¹).1.mulVec (c • x)) +
          standardQuadraticForm (c • x) =
        c * (standardQuadraticForm ((g⁻¹).1.mulVec x) + standardQuadraticForm x)
    rw [Matrix.mulVec_smul]
    have hc : c ^ 2 = c := by
      revert c
      decide
    simp [standardQuadraticForm]
    ring_nf
    rw [hc]

def symplecticFunctional (d : ModTwoSpace) :
    ModTwoSpace →ₗ[ZMod 2] ZMod 2 where
  toFun w := modTwoSymplecticForm d w
  map_add' := modTwoSymplecticForm_add_right d
  map_smul' c w := by
    simp [modTwoSymplecticForm]
    ring

theorem finiteQuadraticCocycle_defining_identity
    (g : ModTwoSymplecticGroup) (w : ModTwoSpace) :
    standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w =
      modTwoSymplecticForm (finiteQuadraticCocycle g) w := by
  have heq :
      quadraticDefectLinear g =
        symplecticFunctional (finiteQuadraticCocycle g) := by
    apply (Pi.basisFun (ZMod 2) SymplecticIndex).ext
    intro i
    rcases i with i | i
    · fin_cases i <;>
        simp [quadraticDefectLinear, symplecticFunctional, finiteQuadraticCocycle,
          modTwoSymplecticForm, modTwoBasis, Pi.basisFun]
    · fin_cases i <;>
        simp [quadraticDefectLinear, symplecticFunctional, finiteQuadraticCocycle,
          modTwoSymplecticForm, modTwoBasis, Pi.basisFun]
  exact LinearMap.congr_fun heq w

theorem modTwoSymplecticForm_nondegenerate {x y : ModTwoSpace}
    (h : ∀ w, modTwoSymplecticForm x w = modTwoSymplecticForm y w) :
    x = y := by
  funext i
  rcases i with i | i
  · fin_cases i
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inr 0))
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inr 1))
  · fin_cases i
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inl 0))
    · simpa [modTwoSymplecticForm, modTwoBasis] using
        h (modTwoBasis (Sum.inl 1))

theorem modTwoSymplecticForm_add_left (x y z : ModTwoSpace) :
    modTwoSymplecticForm (x + y) z =
      modTwoSymplecticForm x z + modTwoSymplecticForm y z := by
  simp [modTwoSymplecticForm, add_mul, Finset.sum_add_distrib]
  abel

theorem modTwoSymplecticForm_smul_left
    (g : ModTwoSymplecticGroup) (x y : ModTwoSpace) :
    modTwoSymplecticForm (g • x) y =
      modTwoSymplecticForm x (g⁻¹ • y) := by
  rw [← modTwoSymplecticForm_smul g x (g⁻¹ • y)]
  simp

theorem finiteQuadraticCocycle_isCocycle :
    groupCohomology.IsCocycle₁ finiteQuadraticCocycle := by
  intro g h
  apply modTwoSymplecticForm_nondegenerate
  intro w
  rw [← finiteQuadraticCocycle_defining_identity]
  rw [modTwoSymplecticForm_add_left, modTwoSymplecticForm_smul_left]
  rw [← finiteQuadraticCocycle_defining_identity]
  rw [← finiteQuadraticCocycle_defining_identity]
  rw [_root_.mul_inv_rev]
  simp only [mul_smul]
  have hcancel :
      standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm (g⁻¹ • w) = 0 :=
    CharTwo.add_self_eq_zero _
  rw [← add_zero
    (standardQuadraticForm (h⁻¹ • g⁻¹ • w) + standardQuadraticForm w),
    ← hcancel]
  abel

def integralQuadraticCocycle (g : IntegralSymplecticGroup) : ModTwoSpace :=
  finiteQuadraticCocycle (reducedSymplecticHom g)

theorem reducedSymplecticHom_smul
    (g : IntegralSymplecticGroup) (w : ModTwoSpace) :
    reducedSymplecticHom g • w = g • w :=
  rfl

theorem integralQuadraticCocycle_defining_identity
    (g : IntegralSymplecticGroup) (w : ModTwoSpace) :
    standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w =
      modTwoSymplecticForm (integralQuadraticCocycle g) w := by
  rw [← reducedSymplecticHom_smul g⁻¹ w, map_inv]
  exact finiteQuadraticCocycle_defining_identity (reducedSymplecticHom g) w

theorem integralQuadraticCocycle_isCocycle :
    groupCohomology.IsCocycle₁ integralQuadraticCocycle := by
  intro g h
  change finiteQuadraticCocycle (reducedSymplecticHom (g * h)) =
    g • finiteQuadraticCocycle (reducedSymplecticHom h) +
      finiteQuadraticCocycle (reducedSymplecticHom g)
  rw [map_mul, ← reducedSymplecticHom_smul]
  exact finiteQuadraticCocycle_isCocycle
    (reducedSymplecticHom g) (reducedSymplecticHom h)

def lowerShear (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.transpose = B) :
    IntegralSymplecticGroup :=
  ⟨Matrix.fromBlocks 1 0 B 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [hB]⟩

def lowerShearB1 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def lowerShearB2 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

def lowerShearB12 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun _ _ => 1

theorem lowerShearB1_symm : lowerShearB1.transpose = lowerShearB1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem lowerShearB2_symm : lowerShearB2.transpose = lowerShearB2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem lowerShearB12_symm : lowerShearB12.transpose = lowerShearB12 :=
  rfl

def transvectionF1 : IntegralSymplecticGroup :=
  lowerShear lowerShearB1 lowerShearB1_symm

def transvectionF2 : IntegralSymplecticGroup :=
  lowerShear lowerShearB2 lowerShearB2_symm

def transvectionF12 : IntegralSymplecticGroup :=
  lowerShear lowerShearB12 lowerShearB12_symm

def transvectionWitness (u : ModTwoSpace) : IntegralSymplecticGroup :=
  if u (Sum.inl 1) = 0 then transvectionF2
  else if u (Sum.inl 0) = 0 then transvectionF1
  else transvectionF12

theorem transvectionWitness_ne (u : ModTwoSpace) :
    transvectionWitness u • u - u ≠
      integralQuadraticCocycle (transvectionWitness u) := by
  revert u
  decide

theorem integralQuadraticCocycle_not_isCoboundary :
    ¬groupCohomology.IsCoboundary₁ integralQuadraticCocycle := by
  rintro ⟨u, hu⟩
  exact transvectionWitness_ne u (hu (transvectionWitness u))

def upperShear (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.transpose = B) :
    IntegralSymplecticGroup :=
  ⟨Matrix.fromBlocks 1 B 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [hB]⟩

def upperTransvectionE1 : IntegralSymplecticGroup :=
  upperShear lowerShearB1 lowerShearB1_symm

def upperTransvectionE2 : IntegralSymplecticGroup :=
  upperShear lowerShearB2 lowerShearB2_symm

theorem fixed_by_four_shears_eq_zero
    (u : ModTwoSpace)
    (hl1 : transvectionF1 • u = u)
    (hl2 : transvectionF2 • u = u)
    (hu1 : upperTransvectionE1 • u = u)
    (hu2 : upperTransvectionE2 • u = u) :
    u = 0 := by
  revert u
  decide

theorem modTwo_fixed_by_integralSymplecticGroup_eq_zero
    (u : ModTwoSpace) (h : ∀ g : IntegralSymplecticGroup, g • u = u) :
    u = 0 :=
  fixed_by_four_shears_eq_zero u
    (h transvectionF1) (h transvectionF2)
    (h upperTransvectionE1) (h upperTransvectionE2)

def centralNegOne : IntegralSymplecticGroup :=
  ⟨-1, SymplecticGroup.neg_mem (by simp)⟩

theorem centralNegOne_smul (v : IntegralLattice) :
    centralNegOne • v = -v := by
  funext i
  simp [centralNegOne]

theorem centralNegOne_comm (g : IntegralSymplecticGroup) :
    centralNegOne * g = g * centralNegOne := by
  apply Subtype.ext
  simp [centralNegOne]

theorem integralOneCocycles_areCoboundaries
    (F : IntegralSymplecticGroup → IntegralLattice)
    (hF : groupCohomology.IsCocycle₁ F) :
    groupCohomology.IsCoboundary₁ F := by
  let t0 := F centralNegOne
  have htwo (g : IntegralSymplecticGroup) :
      (2 : ℕ) • F g = t0 - g • t0 := by
    have hzg := hF centralNegOne g
    have hgz := hF g centralNegOne
    rw [centralNegOne_comm] at hzg
    rw [centralNegOne_smul] at hzg
    dsimp [t0]
    rw [hgz] at hzg
    apply (eq_sub_iff_add_eq).2
    rw [two_nsmul]
    calc
      F g + F g + g • F centralNegOne =
          (g • F centralNegOne + F g) + F g := by abel
      _ = (-F g + F centralNegOne) + F g := by rw [hzg]
      _ = F centralNegOne := by abel
  have ht0fixed (g : IntegralSymplecticGroup) :
      g • reduceVector t0 = reduceVector t0 := by
    have hred := congrArg reduceVector (htwo g)
    rw [map_nsmul, map_sub, reduceVector_smul] at hred
    have hexp := modTwoSpace_exponent_two (reduceVector (F g))
    rw [hexp] at hred
    exact (sub_eq_zero.mp hred.symm).symm
  have ht0zero : reduceVector t0 = 0 :=
    modTwo_fixed_by_integralSymplecticGroup_eq_zero _ ht0fixed
  obtain ⟨u0, hu0⟩ := exists_half_of_reduceVector_eq_zero t0 ht0zero
  refine ⟨-u0, ?_⟩
  intro g
  apply two_nsmul_integralLattice_injective
  change (2 : ℕ) •
      ((DistribSMul.toAddMonoidHom IntegralLattice g) (-u0) - (-u0)) =
    (2 : ℕ) • F g
  rw [nsmul_sub, map_neg, neg_nsmul, neg_nsmul]
  have hg := map_nsmul
    (DistribSMul.toAddMonoidHom IntegralLattice g) 2 u0
  rw [← hg, hu0, htwo]
  rw [sub_neg_eq_add]
  change -(g • t0) + t0 = t0 - g • t0
  abel

def integralSymplecticCocycleInput : IntegralSymplecticCocycleInput where
  d := integralQuadraticCocycle
  defining_identity := integralQuadraticCocycle_defining_identity
  cocycle := integralQuadraticCocycle_isCocycle
  not_coboundary := integralQuadraticCocycle_not_isCoboundary
  integral_one_cocycles_are_coboundaries :=
    integralOneCocycles_areCoboundaries

end ConnesRigidity

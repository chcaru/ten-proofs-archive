
import ConnesRigidity.ArithmeticCocycle

namespace ConnesRigidity

universe u v w

namespace ModTwoLiftingData

variable {G : Type u} {V : Type v} {W : Type w}
variable [Group G] [AddCommGroup V] [AddCommGroup W]
variable [DistribMulAction G V] [DistribMulAction G W]

variable (D : ModTwoLiftingData G V W)
variable (d : G → W)

noncomputable def liftedExtensionEmbedding
    (hd : groupCohomology.IsCocycle₁ d) :
    CocycleExtension (D.liftedTwoCocycle d hd) →*
      CocycleExtension
        (NormalizedAddCocycle.zero : NormalizedAddCocycle G V) where
  toFun x :=
    { fst := (2 : ℕ) • x.fst + D.liftedOneCochain d x.snd
      snd := x.snd }
  map_one' := by
    apply CocycleExtension.ext
    · simp [D.liftedOneCochain_one d hd]
    · simp
  map_mul' x y := by
    apply CocycleExtension.ext
    · simp only [CocycleExtension.mul_fst, NormalizedAddCocycle.zero_apply,
        CocycleExtension.mul_snd, add_zero, smul_add]
      have hc := D.two_nsmul_liftedTwoCocycle d hd x.snd y.snd
      simp only [liftDefect] at hc
      rw [hc]
      rw [show (2 : ℕ) • (x.snd • y.fst) =
        x.snd • ((2 : ℕ) • y.fst) by
          exact ((DistribSMul.toAddMonoidHom V x.snd).map_nsmul _ _).symm]
      abel
    · rfl

@[simp]
theorem liftedExtensionEmbedding_fst
    (hd : groupCohomology.IsCocycle₁ d)
    (x : CocycleExtension (D.liftedTwoCocycle d hd)) :
    (D.liftedExtensionEmbedding d hd x).fst =
      (2 : ℕ) • x.fst + D.liftedOneCochain d x.snd :=
  rfl

@[simp]
theorem liftedExtensionEmbedding_snd
    (hd : groupCohomology.IsCocycle₁ d)
    (x : CocycleExtension (D.liftedTwoCocycle d hd)) :
    (D.liftedExtensionEmbedding d hd x).snd = x.snd :=
  rfl

theorem liftedExtensionEmbedding_injective
    (hd : groupCohomology.IsCocycle₁ d) :
    Function.Injective (D.liftedExtensionEmbedding d hd) := by
  intro x y hxy
  have hsnd : x.snd = y.snd := by
    exact congr_arg
      (fun z : CocycleExtension
        (NormalizedAddCocycle.zero : NormalizedAddCocycle G V) ↦ z.snd) hxy
  apply CocycleExtension.ext
  · apply D.two_nsmul_injective
    have hfst := congr_arg CocycleExtension.fst hxy
    simp only [liftedExtensionEmbedding_fst] at hfst hsnd
    rw [hsnd] at hfst
    exact add_right_cancel hfst
  · exact hsnd

theorem mem_range_liftedExtensionEmbedding_iff
    (hd : groupCohomology.IsCocycle₁ d)
    (z : CocycleExtension
      (NormalizedAddCocycle.zero : NormalizedAddCocycle G V)) :
    z ∈ MonoidHom.range (D.liftedExtensionEmbedding d hd) ↔
      D.reduce z.fst = d z.snd := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [map_add, map_nsmul, D.exponent_two]
  · intro hz
    have hred :
        D.reduce (z.fst - D.liftedOneCochain d z.snd) = 0 := by
      rw [map_sub, D.reduce_liftedOneCochain, hz, sub_self]
    obtain ⟨u, hu⟩ := D.exists_half_of_reduce_eq_zero
      (z.fst - D.liftedOneCochain d z.snd) hred
    refine ⟨{ fst := u, snd := z.snd }, ?_⟩
    apply CocycleExtension.ext
    · simp only [liftedExtensionEmbedding_fst]
      rw [hu]
      abel
    · rfl

def splitExtensionRepresentative (w : W) :
    CocycleExtension
      (NormalizedAddCocycle.zero : NormalizedAddCocycle G V) :=
  { fst := D.lift w, snd := 1 }

theorem exists_image_mul_splitExtensionRepresentative
    (hd : groupCohomology.IsCocycle₁ d)
    (z : CocycleExtension
      (NormalizedAddCocycle.zero : NormalizedAddCocycle G V)) :
    ∃ (x : CocycleExtension (D.liftedTwoCocycle d hd)) (w : W),
      z = D.splitExtensionRepresentative w *
        D.liftedExtensionEmbedding d hd x := by
  let w : W :=
    D.reduce (z.fst - D.liftedOneCochain d z.snd)
  let remainder : V :=
    z.fst - D.liftedOneCochain d z.snd - D.lift w
  have hred : D.reduce remainder = 0 := by
    dsimp [remainder, w]
    rw [map_sub, map_sub, D.reduce_lift,
      D.reduce_liftedOneCochain]
    abel
  obtain ⟨u, hu⟩ := D.exists_half_of_reduce_eq_zero remainder hred
  refine ⟨{ fst := u, snd := z.snd }, w, ?_⟩
  apply CocycleExtension.ext
  · simp only [CocycleExtension.mul_fst, liftedExtensionEmbedding_fst,
      liftedExtensionEmbedding_snd, splitExtensionRepresentative,
      NormalizedAddCocycle.zero_apply, add_zero]
    rw [hu]
    dsimp [remainder]
    simp only [one_smul]
    abel
  · simp [splitExtensionRepresentative]

theorem liftedExtensionEmbedding_range_finiteIndex
    [Finite W]
    (hd : groupCohomology.IsCocycle₁ d) :
    (MonoidHom.range (D.liftedExtensionEmbedding d hd)).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  let S : Subgroup
      (CocycleExtension
        (NormalizedAddCocycle.zero : NormalizedAddCocycle G V)) :=
    MonoidHom.range (D.liftedExtensionEmbedding d hd)
  let reps : W → (CocycleExtension
      (NormalizedAddCocycle.zero : NormalizedAddCocycle G V) ⧸ S) :=
    fun w ↦ QuotientGroup.mk (D.splitExtensionRepresentative w)
  apply Finite.of_surjective reps
  intro q
  induction q using Quotient.inductionOn with
  | _ z =>
      obtain ⟨x, w, hz⟩ :=
        D.exists_image_mul_splitExtensionRepresentative d hd z
      refine ⟨w, ?_⟩
      change QuotientGroup.mk (D.splitExtensionRepresentative w) =
        QuotientGroup.mk z
      apply Quotient.sound
      change QuotientGroup.leftRel S
        (D.splitExtensionRepresentative w) z
      apply QuotientGroup.leftRel_apply.mpr
      rw [hz]
      simp only [inv_mul_cancel_left]
      exact ⟨x, rfl⟩

end ModTwoLiftingData

noncomputable def gammaOneToGammaZero :
    integralSymplecticCocycleInput.GammaOne →*
      IntegralSymplecticCocycleInput.GammaZero :=
  symplecticModTwoLiftingData.liftedExtensionEmbedding
    integralQuadraticCocycle integralQuadraticCocycle_isCocycle

theorem gammaOneToGammaZero_injective :
    Function.Injective gammaOneToGammaZero :=
  symplecticModTwoLiftingData.liftedExtensionEmbedding_injective
    integralQuadraticCocycle integralQuadraticCocycle_isCocycle

theorem gammaOneToGammaZero_range_finiteIndex :
    (MonoidHom.range gammaOneToGammaZero).FiniteIndex :=
  symplecticModTwoLiftingData.liftedExtensionEmbedding_range_finiteIndex
    integralQuadraticCocycle integralQuadraticCocycle_isCocycle

end ConnesRigidity

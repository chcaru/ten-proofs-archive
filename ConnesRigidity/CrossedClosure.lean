


import ConnesRigidity.CrossedMultipliers















namespace ConnesRigidity

open MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusActionL2Equiv_one :
    torusActionL2Equiv (1 : IntegralSymplecticGroup) =
      LinearIsometryEquiv.refl ℂ TorusL2 := by
  apply LinearIsometryEquiv.ext
  intro f
  apply Lp.ext
  filter_upwards [torusActionL2Equiv_coeFn 1 f] with t ht
  simpa using ht

theorem explicitCrossedRegularEquiv_kernel
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice)
    (v : IntegralLattice) :
    explicitCrossedRegularEquiv c
        ({ fst := v, snd := 1 } : CocycleExtension c) =
      crossedCharacterDiagonalEquiv v := by
  apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
  apply ContinuousLinearEquiv.coe_injective
  refine lp.ext_continuousLinearMap
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) fun k => ?_
  apply ContinuousLinearMap.ext
  intro f
  change
    explicitCrossedRegularEquiv c
        ({ fst := v, snd := 1 } : CocycleExtension c)
        (lp.single 2 k f) =
      crossedCharacterDiagonalEquiv v (lp.single 2 k f)
  rw [explicitCrossedRegularEquiv_single]
  simp only [NormalizedAddCocycle.one_left, add_zero,
    one_mul, inv_one]
  rw [torusActionL2Equiv_one]
  exact crossedCharacterDiagonalEquiv_single v k f |>.symm

theorem crossedCochainScalarEquiv_one :
    crossedCochainScalarEquiv (1 : IntegralSymplecticGroup) =
      LinearIsometryEquiv.refl ℂ CrossedHilbert := by
  apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
  apply ContinuousLinearEquiv.coe_injective
  refine lp.ext_continuousLinearMap
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) fun k => ?_
  apply ContinuousLinearMap.ext
  intro f
  change crossedCochainScalarEquiv 1 (lp.single 2 k f) =
    (lp.single 2 k f : CrossedHilbert)
  rw [crossedCochainScalarEquiv_single]
  apply congrArg (fun h : TorusL2 =>
    (lp.single 2 k h : CrossedHilbert))
  apply Lp.ext
  filter_upwards [
    torusCochainInverseMultiplierEquiv_coeFn 1 f] with t ht
  rw [ht, torusCochain_one]
  simp

theorem commute_star_linearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (T : H →L[ℂ] H) (e : H ≃ₗᵢ[ℂ] H)
    (h : Commute T (e : H →L[ℂ] H)) :
    Commute T (star (e : H →L[ℂ] H)) := by
  let u : unitary (H →L[ℂ] H) :=
    Unitary.linearIsometryEquiv.symm e
  have hu : (u : H →L[ℂ] H) = (e : H →L[ℂ] H) := rfl
  have hleft :
      star (e : H →L[ℂ] H) * (e : H →L[ℂ] H) = 1 := by
    simpa [hu] using Unitary.coe_star_mul_self u
  have hright :
      (e : H →L[ℂ] H) * star (e : H →L[ℂ] H) = 1 := by
    simpa [hu] using Unitary.coe_mul_star_self u
  change T * star (e : H →L[ℂ] H) =
    star (e : H →L[ℂ] H) * T
  calc
    T * star (e : H →L[ℂ] H) =
        (star (e : H →L[ℂ] H) * (e : H →L[ℂ] H)) *
          (T * star (e : H →L[ℂ] H)) := by rw [hleft, one_mul]
    _ = star (e : H →L[ℂ] H) *
        ((e : H →L[ℂ] H) * T) *
          star (e : H →L[ℂ] H) := by simp only [mul_assoc]
    _ = star (e : H →L[ℂ] H) *
        (T * (e : H →L[ℂ] H)) *
          star (e : H →L[ℂ] H) := by rw [← h.eq]
    _ = (star (e : H →L[ℂ] H) * T) *
        ((e : H →L[ℂ] H) * star (e : H →L[ℂ] H)) := by
          simp only [mul_assoc]
    _ = star (e : H →L[ℂ] H) * T := by rw [hright, mul_one]

abbrev CrossedOperator :=
  CrossedHilbert →L[ℂ] CrossedHilbert

def zeroDiagonalGenerator
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    CrossedOperator :=
  diagonalConjugatedZeroRegularEquiv a g

def twistedGenerator
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    CrossedOperator :=
  explicitCrossedRegularEquiv
    integralSymplecticCocycleInput.twoCocycle
    (twistedExtensionElement a g)

def cochainScalarOperator (g : IntegralSymplecticGroup) :
    CrossedOperator :=
  crossedCochainScalarEquiv g

def characterDiagonalOperator (v : IntegralLattice) :
    CrossedOperator :=
  crossedCharacterDiagonalEquiv v

theorem zeroDiagonalGenerator_eq
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    zeroDiagonalGenerator a g =
      cochainScalarOperator g * twistedGenerator a g := by
  rw [zeroDiagonalGenerator,
    torusCochainDiagonal_conjugates_regular]
  unfold cochainCorrectedTwistedRegularEquiv
  unfold cochainScalarOperator twistedGenerator
  apply ContinuousLinearMap.ext
  intro ξ
  rfl

theorem twistedGenerator_kernel (v : IntegralLattice) :
    twistedGenerator v 1 = characterDiagonalOperator v := by
  exact congrArg
    (fun e : CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert =>
      (e : CrossedOperator))
    (explicitCrossedRegularEquiv_kernel
      integralSymplecticCocycleInput.twoCocycle v)

theorem cochainScalarOperator_one :
    cochainScalarOperator 1 = 1 := by
  exact congrArg
    (fun e : CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert =>
      (e : CrossedOperator))
    crossedCochainScalarEquiv_one

theorem zeroDiagonalGenerator_kernel (v : IntegralLattice) :
    zeroDiagonalGenerator v 1 = characterDiagonalOperator v := by
  rw [zeroDiagonalGenerator_eq, cochainScalarOperator_one,
    one_mul, twistedGenerator_kernel]

private theorem commute_mul_of_commute
    (T X Y : CrossedOperator)
    (hX : Commute T X) (hY : Commute T Y) :
    Commute T (X * Y) := by
  calc
    T * (X * Y) = (T * X) * Y := by rw [mul_assoc]
    _ = (X * T) * Y := by rw [hX.eq]
    _ = X * (T * Y) := by rw [mul_assoc]
    _ = X * (Y * T) := by rw [hY.eq]
    _ = (X * Y) * T := by rw [mul_assoc]

private theorem star_cochainScalarOperator_mul_self
    (g : IntegralSymplecticGroup) :
    star (cochainScalarOperator g) * cochainScalarOperator g = 1 := by
  let u : unitary CrossedOperator :=
    Unitary.linearIsometryEquiv.symm (crossedCochainScalarEquiv g)
  have hu :
      (u : CrossedOperator) = cochainScalarOperator g := rfl
  simpa [hu] using Unitary.coe_star_mul_self u

theorem commute_twisted_of_commute_zeroDiagonal
    (T : CrossedOperator)
    (hT : ∀ a : IntegralLattice, ∀ g : IntegralSymplecticGroup,
      Commute T (zeroDiagonalGenerator a g))
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    Commute T (twistedGenerator a g) := by
  have hchar : ∀ v : IntegralLattice,
      Commute T (characterDiagonalOperator v) := by
    intro v
    rw [← zeroDiagonalGenerator_kernel]
    exact hT v 1
  have hZ : Commute T (cochainScalarOperator g) :=
    commute_crossedCochainScalar_of_commute_characters T hchar g
  have hZstar : Commute T (star (cochainScalarOperator g)) :=
    commute_star_linearIsometryEquiv T
      (crossedCochainScalarEquiv g) hZ
  have hA : Commute T (zeroDiagonalGenerator a g) :=
    hT a g
  rw [zeroDiagonalGenerator_eq] at hA
  have hprod :=
    commute_mul_of_commute T
      (star (cochainScalarOperator g))
      (cochainScalarOperator g * twistedGenerator a g)
      hZstar hA
  have hfactor :
      star (cochainScalarOperator g) *
          (cochainScalarOperator g * twistedGenerator a g) =
        twistedGenerator a g := by
    rw [← mul_assoc, star_cochainScalarOperator_mul_self, one_mul]
  rw [hfactor] at hprod
  exact hprod

theorem commute_zeroDiagonal_of_commute_twisted
    (T : CrossedOperator)
    (hT : ∀ a : IntegralLattice, ∀ g : IntegralSymplecticGroup,
      Commute T (twistedGenerator a g))
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    Commute T (zeroDiagonalGenerator a g) := by
  have hchar : ∀ v : IntegralLattice,
      Commute T (characterDiagonalOperator v) := by
    intro v
    rw [← twistedGenerator_kernel]
    exact hT v 1
  have hZ : Commute T (cochainScalarOperator g) :=
    commute_crossedCochainScalar_of_commute_characters T hchar g
  rw [zeroDiagonalGenerator_eq]
  exact commute_mul_of_commute T _ _ hZ (hT a g)

def zeroDiagonalGeneratorSet : Set CrossedOperator :=
  Set.range fun p :
      IntegralLattice × IntegralSymplecticGroup =>
    zeroDiagonalGenerator p.1 p.2

def twistedGeneratorSet : Set CrossedOperator :=
  Set.range fun p :
      IntegralLattice × IntegralSymplecticGroup =>
    twistedGenerator p.1 p.2

theorem mem_zeroDiagonalGeneratorSet_centralizer_iff
    (T : CrossedOperator) :
    T ∈ StarSubalgebra.centralizer ℂ zeroDiagonalGeneratorSet ↔
      ∀ a : IntegralLattice, ∀ g : IntegralSymplecticGroup,
        Commute T (zeroDiagonalGenerator a g) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a g
    have hg := h (zeroDiagonalGenerator a g)
      (show zeroDiagonalGenerator a g ∈
          zeroDiagonalGeneratorSet from
        ⟨(a, g), rfl⟩)
    exact hg.1.symm
  · intro h x hx
    obtain ⟨⟨a, g⟩, rfl⟩ := hx
    constructor
    · exact (h a g).eq.symm
    · have hs :=
        commute_star_linearIsometryEquiv T
          (diagonalConjugatedZeroRegularEquiv a g) (h a g)
      exact hs.eq.symm

theorem mem_twistedGeneratorSet_centralizer_iff
    (T : CrossedOperator) :
    T ∈ StarSubalgebra.centralizer ℂ twistedGeneratorSet ↔
      ∀ a : IntegralLattice, ∀ g : IntegralSymplecticGroup,
        Commute T (twistedGenerator a g) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a g
    have hg := h (twistedGenerator a g)
      (show twistedGenerator a g ∈ twistedGeneratorSet from
        ⟨(a, g), rfl⟩)
    exact hg.1.symm
  · intro h x hx
    obtain ⟨⟨a, g⟩, rfl⟩ := hx
    constructor
    · exact (h a g).eq.symm
    · have hs :=
        commute_star_linearIsometryEquiv T
          (explicitCrossedRegularEquiv
            integralSymplecticCocycleInput.twoCocycle
            (twistedExtensionElement a g)) (h a g)
      exact hs.eq.symm

theorem zeroDiagonal_twisted_firstCommutants_eq :
    StarSubalgebra.centralizer ℂ zeroDiagonalGeneratorSet =
      StarSubalgebra.centralizer ℂ twistedGeneratorSet := by
  ext T
  rw [mem_zeroDiagonalGeneratorSet_centralizer_iff,
    mem_twistedGeneratorSet_centralizer_iff]
  constructor
  · intro h a g
    exact commute_twisted_of_commute_zeroDiagonal T h a g
  · intro h a g
    exact commute_zeroDiagonal_of_commute_twisted T h a g

theorem zeroDiagonal_twisted_vonNeumannClosure_eq :
    vonNeumannClosure zeroDiagonalGeneratorSet =
      vonNeumannClosure twistedGeneratorSet := by
  apply VonNeumannAlgebra.ext
  intro T
  exact Iff.of_eq <| congrArg
    (fun S : StarSubalgebra ℂ CrossedOperator =>
      T ∈ StarSubalgebra.centralizer ℂ (S : Set CrossedOperator))
    zeroDiagonal_twisted_firstCommutants_eq

def crossedRegularGeneratorSet
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice) :
    Set CrossedOperator :=
  Set.range fun x : CocycleExtension c =>
    (explicitCrossedRegularEquiv c x : CrossedOperator)

theorem twistedGeneratorSet_eq_crossedRegular :
    twistedGeneratorSet =
      crossedRegularGeneratorSet
        integralSymplecticCocycleInput.twoCocycle := by
  ext T
  constructor
  · rintro ⟨⟨a, g⟩, rfl⟩
    exact ⟨⟨a, g⟩, rfl⟩
  · rintro ⟨⟨a, g⟩, rfl⟩
    exact ⟨⟨a, g⟩, rfl⟩

def cochainConjugation :
    CrossedOperator ≃⋆ₐ[ℂ] CrossedOperator :=
  torusCochainDiagonalEquiv.conjStarAlgEquiv

theorem cochainConjugation_zeroRegular
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    cochainConjugation
        (explicitCrossedRegularEquiv
          (NormalizedAddCocycle.zero :
            NormalizedAddCocycle
              IntegralSymplecticGroup IntegralLattice)
          (zeroExtensionElement a g) : CrossedOperator) =
      zeroDiagonalGenerator a g := by
  apply ContinuousLinearMap.ext
  intro ξ
  rfl

theorem zeroDiagonalGeneratorSet_eq_image :
    zeroDiagonalGeneratorSet =
      cochainConjugation ''
        crossedRegularGeneratorSet
          (NormalizedAddCocycle.zero :
            NormalizedAddCocycle
              IntegralSymplecticGroup IntegralLattice) := by
  ext T
  constructor
  · rintro ⟨⟨a, g⟩, rfl⟩
    refine ⟨
      (explicitCrossedRegularEquiv
        (NormalizedAddCocycle.zero :
          NormalizedAddCocycle
            IntegralSymplecticGroup IntegralLattice)
        (zeroExtensionElement a g) : CrossedOperator), ?_, ?_⟩
    · exact ⟨zeroExtensionElement a g, rfl⟩
    · exact cochainConjugation_zeroRegular a g
  · rintro ⟨T, ⟨⟨a, g⟩, rfl⟩, rfl⟩
    exact ⟨(a, g), cochainConjugation_zeroRegular a g⟩

theorem conjStarAlgEquiv_mem_centralizer_image_iff
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    e.conjStarAlgEquiv T ∈
        StarSubalgebra.centralizer ℂ (e.conjStarAlgEquiv '' S) ↔
      T ∈ StarSubalgebra.centralizer ℂ S := by
  rw [StarSubalgebra.mem_centralizer_iff,
    StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h x hx
    have hx' := h (e.conjStarAlgEquiv x) ⟨x, hx, rfl⟩
    constructor
    · have heq :
          e.conjStarAlgEquiv (x * T) =
            e.conjStarAlgEquiv (T * x) := by
        rw [map_mul, map_mul]
        exact hx'.1
      exact e.conjStarAlgEquiv.injective heq
    · have heq :
          e.conjStarAlgEquiv (star x * T) =
            e.conjStarAlgEquiv (T * star x) := by
        rw [map_mul, map_mul]
        simpa only [map_star] using hx'.2
      exact e.conjStarAlgEquiv.injective heq
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' := h x hx
    constructor
    · have heq := congrArg e.conjStarAlgEquiv hx'.1
      rw [map_mul, map_mul] at heq
      exact heq
    · have heq := congrArg e.conjStarAlgEquiv hx'.2
      rw [map_mul, map_mul] at heq
      rw [map_star] at heq
      exact heq

theorem conjStarAlgEquiv_image_centralizer
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (S : Set (H →L[ℂ] H)) :
    (StarSubalgebra.centralizer ℂ
        (e.conjStarAlgEquiv '' S) : Set (K →L[ℂ] K)) =
      e.conjStarAlgEquiv ''
        (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.conjStarAlgEquiv.symm y, ?_, ?_⟩
    · apply (conjStarAlgEquiv_mem_centralizer_image_iff
        e S (e.conjStarAlgEquiv.symm y)).mp
      rw [e.conjStarAlgEquiv.apply_symm_apply]
      exact hy
    · exact e.conjStarAlgEquiv.apply_symm_apply y
  · rintro ⟨x, hx, rfl⟩
    exact (conjStarAlgEquiv_mem_centralizer_image_iff
      e S x).mpr hx

theorem conjStarAlgEquiv_mem_vonNeumannClosure_image_iff
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    e.conjStarAlgEquiv T ∈
        vonNeumannClosure (e.conjStarAlgEquiv '' S) ↔
      T ∈ vonNeumannClosure S := by
  change
    e.conjStarAlgEquiv T ∈ StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ
          (e.conjStarAlgEquiv '' S) : Set (K →L[ℂ] K)) ↔
      T ∈ StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))
  rw [conjStarAlgEquiv_image_centralizer e S]
  exact conjStarAlgEquiv_mem_centralizer_image_iff e
    (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) T

def vonNeumannClosureConjStarAlgEquiv
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (S : Set (H →L[ℂ] H)) :
    (vonNeumannClosure S).toStarSubalgebra ≃⋆ₐ[ℂ]
      (vonNeumannClosure
        (e.conjStarAlgEquiv '' S)).toStarSubalgebra where
  toFun x :=
    ⟨e.conjStarAlgEquiv x,
      (conjStarAlgEquiv_mem_vonNeumannClosure_image_iff
        e S x).mpr x.prop⟩
  invFun y :=
    ⟨e.conjStarAlgEquiv.symm y, by
      apply (conjStarAlgEquiv_mem_vonNeumannClosure_image_iff
        e S (e.conjStarAlgEquiv.symm y)).mp
      rw [e.conjStarAlgEquiv.apply_symm_apply]
      exact y.prop⟩
  left_inv x := by
    apply Subtype.ext
    exact e.conjStarAlgEquiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact e.conjStarAlgEquiv.apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul e.conjStarAlgEquiv
      (x : H →L[ℂ] H) (y : H →L[ℂ] H)
  map_add' x y := by
    apply Subtype.ext
    exact map_add e.conjStarAlgEquiv
      (x : H →L[ℂ] H) (y : H →L[ℂ] H)
  map_star' x := by
    apply Subtype.ext
    exact map_star e.conjStarAlgEquiv (x : H →L[ℂ] H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul e.conjStarAlgEquiv c (x : H →L[ℂ] H)

def extensionGroupRegularGeneratorSet
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice) :
    Set (GroupL2 (CocycleExtension c) →L[ℂ]
      GroupL2 (CocycleExtension c)) :=
  Set.range fun x : CocycleExtension c =>
    (leftRegularRepresentation (CocycleExtension c) x :
      GroupL2 (CocycleExtension c) →L[ℂ]
        GroupL2 (CocycleExtension c))

theorem extensionPartialFourier_conj_leftRegular
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice)
    (x : CocycleExtension c) :
    (extensionPartialFourier c).conjStarAlgEquiv
        (leftRegularRepresentation (CocycleExtension c) x :
          GroupL2 (CocycleExtension c) →L[ℂ]
            GroupL2 (CocycleExtension c)) =
      (explicitCrossedRegularEquiv c x : CrossedOperator) := by
  apply ContinuousLinearMap.ext
  intro ξ
  change transportedRegularEquiv c x ξ =
    explicitCrossedRegularEquiv c x ξ
  rw [transportedRegularEquiv_eq_explicitCrossedRegularEquiv]

theorem extensionPartialFourier_image_generators
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice) :
    (extensionPartialFourier c).conjStarAlgEquiv ''
        extensionGroupRegularGeneratorSet c =
      crossedRegularGeneratorSet c := by
  ext T
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (extensionPartialFourier_conj_leftRegular c x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨
      (leftRegularRepresentation (CocycleExtension c) x :
        GroupL2 (CocycleExtension c) →L[ℂ]
          GroupL2 (CocycleExtension c)), ⟨x, rfl⟩, ?_⟩
    exact extensionPartialFourier_conj_leftRegular c x

theorem extensionPartialFourier_mem_crossedClosure_iff
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice)
    (T : GroupL2 (CocycleExtension c) →L[ℂ]
      GroupL2 (CocycleExtension c)) :
    (extensionPartialFourier c).conjStarAlgEquiv T ∈
        vonNeumannClosure (crossedRegularGeneratorSet c) ↔
      T ∈ vonNeumannClosure (extensionGroupRegularGeneratorSet c) := by
  rw [← extensionPartialFourier_image_generators c]
  exact conjStarAlgEquiv_mem_vonNeumannClosure_image_iff
    (extensionPartialFourier c)
      (extensionGroupRegularGeneratorSet c) T

theorem extensionPartialFourier_symm_mem_groupClosure_iff
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice)
    (T : CrossedOperator) :
    (extensionPartialFourier c).symm.conjStarAlgEquiv T ∈
        vonNeumannClosure (extensionGroupRegularGeneratorSet c) ↔
      T ∈ vonNeumannClosure (crossedRegularGeneratorSet c) := by
  constructor
  · intro h
    have h' :=
      (extensionPartialFourier_mem_crossedClosure_iff c
        ((extensionPartialFourier c).symm.conjStarAlgEquiv T)).mpr h
    have heq :
        (extensionPartialFourier c).conjStarAlgEquiv
            ((extensionPartialFourier c).symm.conjStarAlgEquiv T) =
          T := by
      change
        (extensionPartialFourier c).conjStarAlgEquiv
            ((extensionPartialFourier c).conjStarAlgEquiv.symm T) =
          T
      exact
        (extensionPartialFourier c).conjStarAlgEquiv.apply_symm_apply T
    rw [heq] at h'
    exact h'
  · intro h
    apply (extensionPartialFourier_mem_crossedClosure_iff c
      ((extensionPartialFourier c).symm.conjStarAlgEquiv T)).mp
    have heq :
        (extensionPartialFourier c).conjStarAlgEquiv
            ((extensionPartialFourier c).symm.conjStarAlgEquiv T) =
          T := by
      change
        (extensionPartialFourier c).conjStarAlgEquiv
            ((extensionPartialFourier c).conjStarAlgEquiv.symm T) =
          T
      exact
        (extensionPartialFourier c).conjStarAlgEquiv.apply_symm_apply T
    rw [heq]
    exact h

theorem cochain_image_zero_vonNeumannClosure_eq_twisted :
    vonNeumannClosure
        (cochainConjugation ''
          crossedRegularGeneratorSet
            (NormalizedAddCocycle.zero :
              NormalizedAddCocycle
                IntegralSymplecticGroup IntegralLattice)) =
      vonNeumannClosure
        (crossedRegularGeneratorSet
          integralSymplecticCocycleInput.twoCocycle) := by
  calc
    _ = vonNeumannClosure zeroDiagonalGeneratorSet :=
      congrArg vonNeumannClosure zeroDiagonalGeneratorSet_eq_image.symm
    _ = vonNeumannClosure twistedGeneratorSet :=
      zeroDiagonal_twisted_vonNeumannClosure_eq
    _ = _ := congrArg vonNeumannClosure
      twistedGeneratorSet_eq_crossedRegular

theorem cochainConjugation_mem_twistedClosure_iff
    (T : CrossedOperator) :
    cochainConjugation T ∈
        vonNeumannClosure
          (crossedRegularGeneratorSet
            integralSymplecticCocycleInput.twoCocycle) ↔
      T ∈
        vonNeumannClosure
          (crossedRegularGeneratorSet
            (NormalizedAddCocycle.zero :
              NormalizedAddCocycle
                IntegralSymplecticGroup IntegralLattice)) := by
  rw [← cochain_image_zero_vonNeumannClosure_eq_twisted]
  exact conjStarAlgEquiv_mem_vonNeumannClosure_image_iff
    torusCochainDiagonalEquiv
    (crossedRegularGeneratorSet
      (NormalizedAddCocycle.zero :
        NormalizedAddCocycle
          IntegralSymplecticGroup IntegralLattice)) T

abbrev ZeroCocycle :
    NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice :=
  NormalizedAddCocycle.zero

abbrev TwistedCocycle :
    NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice :=
  integralSymplecticCocycleInput.twoCocycle

def groupFactorHilbertEquiv :
    GroupL2 (CocycleExtension ZeroCocycle) ≃ₗᵢ[ℂ]
      GroupL2 (CocycleExtension TwistedCocycle) :=
  (extensionPartialFourier ZeroCocycle).trans <|
    torusCochainDiagonalEquiv.trans <|
      (extensionPartialFourier TwistedCocycle).symm

def groupFactorConjugation :
    (GroupL2 (CocycleExtension ZeroCocycle) →L[ℂ]
        GroupL2 (CocycleExtension ZeroCocycle)) ≃⋆ₐ[ℂ]
      (GroupL2 (CocycleExtension TwistedCocycle) →L[ℂ]
        GroupL2 (CocycleExtension TwistedCocycle)) :=
  (extensionPartialFourier ZeroCocycle).conjStarAlgEquiv.trans <|
    torusCochainDiagonalEquiv.conjStarAlgEquiv.trans <|
      (extensionPartialFourier TwistedCocycle).symm.conjStarAlgEquiv

theorem groupFactorConjugation_eq_hilbert :
    groupFactorConjugation =
      groupFactorHilbertEquiv.conjStarAlgEquiv :=
  rfl

theorem groupFactorConjugation_mem_iff
    (T : GroupL2 (CocycleExtension ZeroCocycle) →L[ℂ]
      GroupL2 (CocycleExtension ZeroCocycle)) :
    groupFactorConjugation T ∈
        vonNeumannClosure
          (extensionGroupRegularGeneratorSet TwistedCocycle) ↔
      T ∈
        vonNeumannClosure
          (extensionGroupRegularGeneratorSet ZeroCocycle) := by
  change
    (extensionPartialFourier TwistedCocycle).symm.conjStarAlgEquiv
        (cochainConjugation
          ((extensionPartialFourier ZeroCocycle).conjStarAlgEquiv T)) ∈
        vonNeumannClosure
          (extensionGroupRegularGeneratorSet TwistedCocycle) ↔
      T ∈
        vonNeumannClosure
          (extensionGroupRegularGeneratorSet ZeroCocycle)
  rw [extensionPartialFourier_symm_mem_groupClosure_iff,
    cochainConjugation_mem_twistedClosure_iff,
    extensionPartialFourier_mem_crossedClosure_iff]

def cocycleExtensionDiscreteGroup
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice) :
    CountableDiscreteGroup where
  Carrier := CocycleExtension c
  group := inferInstance
  countable := inferInstance

abbrev constructedGammaZeroGroup : CountableDiscreteGroup :=
  cocycleExtensionDiscreteGroup ZeroCocycle

noncomputable abbrev constructedGammaOneGroup : CountableDiscreteGroup :=
  cocycleExtensionDiscreteGroup TwistedCocycle

theorem groupVonNeumannAlgebra_cocycleExtension
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice) :
    groupVonNeumannAlgebra (cocycleExtensionDiscreteGroup c) =
      vonNeumannClosure (extensionGroupRegularGeneratorSet c) :=
  rfl

def zeroFactorUnderlying
    (x : GroupVonNeumannAlgebra constructedGammaZeroGroup) :
    GroupL2 (CocycleExtension ZeroCocycle) →L[ℂ]
      GroupL2 (CocycleExtension ZeroCocycle) :=
  x.1

def oneFactorUnderlying
    (x : GroupVonNeumannAlgebra constructedGammaOneGroup) :
    GroupL2 (CocycleExtension TwistedCocycle) →L[ℂ]
      GroupL2 (CocycleExtension TwistedCocycle) :=
  x.1

def constructedGroupFactorStarAlgEquiv :
    GroupVonNeumannAlgebra constructedGammaZeroGroup ≃⋆ₐ[ℂ]
    GroupVonNeumannAlgebra constructedGammaOneGroup where
  toFun x :=
    ⟨groupFactorConjugation
        (zeroFactorUnderlying x),
      (groupFactorConjugation_mem_iff
        (zeroFactorUnderlying x)).mpr x.prop⟩
  invFun y :=
    ⟨groupFactorConjugation.symm
        (oneFactorUnderlying y), by
      apply (groupFactorConjugation_mem_iff
        (groupFactorConjugation.symm
          (oneFactorUnderlying y))).mp
      rw [groupFactorConjugation.apply_symm_apply]
      exact y.prop⟩
  left_inv x := by
    apply Subtype.ext
    exact groupFactorConjugation.symm_apply_apply
      (zeroFactorUnderlying x)
  right_inv y := by
    apply Subtype.ext
    exact groupFactorConjugation.apply_symm_apply
      (oneFactorUnderlying y)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul groupFactorConjugation
      (zeroFactorUnderlying x) (zeroFactorUnderlying y)
  map_add' x y := by
    apply Subtype.ext
    exact map_add groupFactorConjugation
      (zeroFactorUnderlying x) (zeroFactorUnderlying y)
  map_star' x := by
    apply Subtype.ext
    exact map_star groupFactorConjugation
      (zeroFactorUnderlying x)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul groupFactorConjugation c
      (zeroFactorUnderlying x)

def crossedVacuum : CrossedHilbert :=
  lp.single 2 (1 : IntegralSymplecticGroup)
    (UnitAddTorus.mFourierLp 2
      (symplecticFourierIndex (0 : IntegralLattice)))

noncomputable def extensionGroupVacuum
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice) :
    GroupL2 (CocycleExtension c) := by
  classical
  exact lp.single 2 (1 : CocycleExtension c) 1

abbrev zeroGroupVacuum :
    GroupL2 (CocycleExtension ZeroCocycle) :=
  extensionGroupVacuum ZeroCocycle

abbrev oneGroupVacuum :
    GroupL2 (CocycleExtension TwistedCocycle) :=
  extensionGroupVacuum TwistedCocycle

theorem extensionPartialFourier_vacuum
    (c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice) :
    extensionPartialFourier c (extensionGroupVacuum c) =
      crossedVacuum := by
  classical
  simpa [extensionGroupVacuum, crossedVacuum] using
    extensionPartialFourier_single c (1 : CocycleExtension c)

theorem torusCochainInverseMultiplierEquiv_one :
    torusCochainInverseMultiplierEquiv
        (1 : IntegralSymplecticGroup) =
      LinearIsometryEquiv.refl ℂ TorusL2 := by
  apply LinearIsometryEquiv.ext
  intro f
  apply Lp.ext
  filter_upwards [
    torusCochainInverseMultiplierEquiv_coeFn 1 f] with t ht
  rw [ht, torusCochain_one]
  simp

theorem torusCochainDiagonalEquiv_vacuum :
    torusCochainDiagonalEquiv crossedVacuum =
      crossedVacuum := by
  rw [crossedVacuum, torusCochainDiagonalEquiv_single,
    torusCochainInverseMultiplierEquiv_one]
  rfl

theorem groupFactorHilbertEquiv_vacuum :
    groupFactorHilbertEquiv zeroGroupVacuum =
      oneGroupVacuum := by
  rw [groupFactorHilbertEquiv, LinearIsometryEquiv.trans_apply,
    zeroGroupVacuum, extensionPartialFourier_vacuum,
    LinearIsometryEquiv.trans_apply,
    torusCochainDiagonalEquiv_vacuum,
    ← extensionPartialFourier_vacuum TwistedCocycle,
    LinearIsometryEquiv.symm_apply_apply]

theorem constructedGroupFactorStarAlgEquiv_trace_preserving
    (x : GroupVonNeumannAlgebra constructedGammaZeroGroup) :
    canonicalTrace constructedGammaOneGroup
        (constructedGroupFactorStarAlgEquiv x) =
      canonicalTrace constructedGammaZeroGroup x := by
  change
    inner ℂ oneGroupVacuum
        (groupFactorConjugation (zeroFactorUnderlying x)
          oneGroupVacuum) =
      inner ℂ zeroGroupVacuum
        (zeroFactorUnderlying x zeroGroupVacuum)
  rw [groupFactorConjugation_eq_hilbert]
  change
    inner ℂ oneGroupVacuum
        (groupFactorHilbertEquiv
          (zeroFactorUnderlying x
            (groupFactorHilbertEquiv.symm oneGroupVacuum))) =
      inner ℂ zeroGroupVacuum
        (zeroFactorUnderlying x zeroGroupVacuum)
  rw [← groupFactorHilbertEquiv_vacuum,
    groupFactorHilbertEquiv.symm_apply_apply]
  exact groupFactorHilbertEquiv.inner_map_map
    zeroGroupVacuum (zeroFactorUnderlying x zeroGroupVacuum)

noncomputable def constructedTracialGroupFactorEquiv :
    TracialGroupFactorEquiv
      constructedGammaZeroGroup constructedGammaOneGroup where
  toStarAlgEquiv := constructedGroupFactorStarAlgEquiv
  normal := starAlgEquiv_isNormal constructedGroupFactorStarAlgEquiv
  trace_preserving :=
    constructedGroupFactorStarAlgEquiv_trace_preserving

theorem constructedGroupFactors_isomorphic :
    TracialGroupFactorsIsomorphic
      constructedGammaZeroGroup constructedGammaOneGroup :=
  ⟨constructedTracialGroupFactorEquiv⟩

end

end ConnesRigidity

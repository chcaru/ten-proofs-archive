
import ConnesRigidity.FactorIsomorphism
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder

namespace ConnesRigidity

open MeasureTheory
open scoped ENNReal
noncomputable section

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def complexUnitBallClip (z : ℂ) : ℂ :=
  (1 / max 1 ‖z‖ : ℝ) • z

theorem continuous_complexUnitBallClip :
    Continuous complexUnitBallClip := by
  unfold complexUnitBallClip
  exact (Continuous.div continuous_const
      (continuous_const.max continuous_norm)
      (fun z => by positivity)).smul continuous_id

theorem complexUnitBallClip_eq_self_of_norm_le
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    complexUnitBallClip z = z := by
  rw [complexUnitBallClip, max_eq_left hz]
  norm_num

theorem complexUnitBallClip_norm_le (z : ℂ) :
    ‖complexUnitBallClip z‖ ≤ 1 := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [complexUnitBallClip_eq_self_of_norm_le hz]
    exact hz
  · have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one (le_of_not_ge hz)
    rw [complexUnitBallClip, max_eq_right (le_of_not_ge hz)]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hzpos)]
    rw [one_div, inv_mul_cancel₀ hzpos.ne']

theorem complexUnitBallClip_sub_norm_le_two
    (z u : ℂ) (hu : ‖u‖ = 1) :
    ‖complexUnitBallClip z - u‖ ≤ 2 * ‖z - u‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [complexUnitBallClip_eq_self_of_norm_le hz]
    nlinarith [norm_nonneg (z - u)]
  · have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
    have hzpos : 0 < ‖z‖ := zero_lt_one.trans hz1
    have hclip :
        complexUnitBallClip z = (1 / ‖z‖ : ℝ) • z := by
      rw [complexUnitBallClip, max_eq_right hz1.le]
    have hdiff :
        ‖complexUnitBallClip z - z‖ = ‖z‖ - 1 := by
      rw [hclip]
      rw [show (1 / ‖z‖ : ℝ) • z - z =
          ((1 / ‖z‖ : ℝ) - 1) • z by module]
      rw [norm_smul, Real.norm_eq_abs]
      have hscalar : |1 / ‖z‖ - 1| = 1 - 1 / ‖z‖ := by
        rw [abs_of_nonpos]
        · ring
        · exact sub_nonpos.mpr ((div_le_one hzpos).mpr hz1.le)
      rw [hscalar]
      field_simp
    have hradial : ‖z‖ - 1 ≤ ‖z - u‖ := by
      rw [← hu]
      exact norm_sub_norm_le z u
    calc
      ‖complexUnitBallClip z - u‖ =
          ‖(complexUnitBallClip z - z) + (z - u)‖ := by
            congr 1
            abel
      _ ≤ ‖complexUnitBallClip z - z‖ + ‖z - u‖ :=
        norm_add_le _ _
      _ ≤ 2 * ‖z - u‖ := by rw [hdiff]; linarith

def measurableUnitFunctionL2
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1) : TorusL2 :=
  (MemLp.of_bound hu.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun t => (hunit t).le)).toLp u

theorem measurableUnitFunctionL2_coeFn
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1) :
    measurableUnitFunctionL2 u hu hunit =ᵐ[volume] u :=
  MemLp.coeFn_toLp _

def clipContinuousMap (c : C(SymplecticTorus, ℂ)) :
    C(SymplecticTorus, ℂ) :=
  ⟨fun t => complexUnitBallClip (c t),
    continuous_complexUnitBallClip.comp c.continuous⟩

theorem clipContinuousMap_norm_le
    (c : C(SymplecticTorus, ℂ)) (t : SymplecticTorus) :
    ‖clipContinuousMap c t‖ ≤ 1 :=
  complexUnitBallClip_norm_le _

theorem clipContinuousMap_toLp_sub_unit_le
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1)
    (c : C(SymplecticTorus, ℂ)) :
    ‖(ContinuousMap.toLp 2 volume ℂ) (clipContinuousMap c) -
        measurableUnitFunctionL2 u hu hunit‖ ≤
      2 * ‖(ContinuousMap.toLp 2 volume ℂ) c -
        measurableUnitFunctionL2 u hu hunit‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub
      ((ContinuousMap.toLp 2 volume ℂ) (clipContinuousMap c))
      (measurableUnitFunctionL2 u hu hunit),
    Lp.coeFn_sub ((ContinuousMap.toLp 2 volume ℂ) c)
      (measurableUnitFunctionL2 u hu hunit),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (clipContinuousMap c),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume c,
    measurableUnitFunctionL2_coeFn u hu hunit
    ] with t hleft hright hclip hc hucoe
  rw [hleft, hright]
  change
    ‖((ContinuousMap.toLp 2 volume ℂ) (clipContinuousMap c)) t -
        measurableUnitFunctionL2 u hu hunit t‖ ≤
      2 * ‖((ContinuousMap.toLp 2 volume ℂ) c) t -
        measurableUnitFunctionL2 u hu hunit t‖
  rw [hclip, hc, hucoe]
  exact complexUnitBallClip_sub_norm_le_two (c t) (u t) (hunit t)

theorem exists_continuous_norm_le_one_approx
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : C(SymplecticTorus, ℂ),
      (∀ t, ‖q t‖ ≤ 1) ∧
      ‖(ContinuousMap.toLp 2 volume ℂ) q -
          measurableUnitFunctionL2 u hu hunit‖ < ε := by
  obtain ⟨c, hc⟩ :=
    (ContinuousMap.toLp_denseRange ℂ volume ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).exists_dist_lt
      (measurableUnitFunctionL2 u hu hunit) (half_pos hε)
  refine ⟨clipContinuousMap c, clipContinuousMap_norm_le c, ?_⟩
  apply lt_of_le_of_lt
    (clipContinuousMap_toLp_sub_unit_le u hu hunit c)
  rw [dist_eq_norm] at hc
  rw [norm_sub_rev]
  linarith

def l2LpTopMultiplier :
    Lp ℂ ∞ (volume : Measure SymplecticTorus) →L[ℂ]
      TorusL2 →L[ℂ] TorusL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2

def continuousTorusMultiplier :
    C(SymplecticTorus, ℂ) →L[ℂ] TorusL2 →L[ℂ] TorusL2 :=
  l2LpTopMultiplier.comp (ContinuousMap.toLp ∞ volume ℂ)

theorem continuousTorusMultiplier_coeFn
    (u : C(SymplecticTorus, ℂ)) (f : TorusL2) :
    continuousTorusMultiplier u f =ᵐ[volume]
      fun t => u t * f t := by
  exact (ContinuousLinearMap.coeFn_holder
    (ContinuousLinearMap.mul ℂ ℂ)
    ((ContinuousMap.toLp ∞ volume ℂ) u) f).trans <| by
      filter_upwards [
        ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) volume u] with t hu
      change ((ContinuousMap.toLp ∞ volume ℂ) u) t * f t =
        u t * f t
      rw [hu]

theorem unitTorusMultiplier_coeFn
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1) (f : TorusL2) :
    l2UnitModulusMultiplierEquiv u hu hunit f =ᵐ[volume]
      fun t => u t * f t :=
  l2UnitModulusMultiplier_coeFn u hu hunit f

theorem continuous_sub_unit_multiplier_norm_le_two
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1)
    (q : C(SymplecticTorus, ℂ))
    (hq : ∀ t, ‖q t‖ ≤ 1) (f : TorusL2) :
    ‖continuousTorusMultiplier q f -
        l2UnitModulusMultiplierEquiv u hu hunit f‖ ≤
      2 * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub (continuousTorusMultiplier q f)
      (l2UnitModulusMultiplierEquiv u hu hunit f),
    continuousTorusMultiplier_coeFn q f,
    unitTorusMultiplier_coeFn u hu hunit f
    ] with t hsub hqcoe hucoe
  rw [hsub]
  change ‖(continuousTorusMultiplier q f) t -
      (l2UnitModulusMultiplierEquiv u hu hunit f) t‖ ≤
    2 * ‖f t‖
  rw [hqcoe, hucoe, ← sub_mul, norm_mul]
  have hqu : ‖q t - u t‖ ≤ 2 := by
    calc
      ‖q t - u t‖ ≤ ‖q t‖ + ‖u t‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [hunit]; linarith [hq t]
  exact mul_le_mul_of_nonneg_right hqu (norm_nonneg _)

theorem continuous_sub_unit_multiplier_on_continuous_norm_le
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1)
    (q h : C(SymplecticTorus, ℂ)) :
    ‖continuousTorusMultiplier q
          ((ContinuousMap.toLp 2 volume ℂ) h) -
        l2UnitModulusMultiplierEquiv u hu hunit
          ((ContinuousMap.toLp 2 volume ℂ) h)‖ ≤
      ‖h‖ * ‖(ContinuousMap.toLp 2 volume ℂ) q -
        measurableUnitFunctionL2 u hu hunit‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub
      (continuousTorusMultiplier q
        ((ContinuousMap.toLp 2 volume ℂ) h))
      (l2UnitModulusMultiplierEquiv u hu hunit
        ((ContinuousMap.toLp 2 volume ℂ) h)),
    continuousTorusMultiplier_coeFn q
      ((ContinuousMap.toLp 2 volume ℂ) h),
    unitTorusMultiplier_coeFn u hu hunit
      ((ContinuousMap.toLp 2 volume ℂ) h),
    Lp.coeFn_sub ((ContinuousMap.toLp 2 volume ℂ) q)
      (measurableUnitFunctionL2 u hu hunit),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume q,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume h,
    measurableUnitFunctionL2_coeFn u hu hunit
    ] with t hout hqmul humul hdiff hqcoe hhcoe hucoe
  rw [hout, hdiff]
  change
    ‖(continuousTorusMultiplier q
          ((ContinuousMap.toLp 2 volume ℂ) h)) t -
        (l2UnitModulusMultiplierEquiv u hu hunit
          ((ContinuousMap.toLp 2 volume ℂ) h)) t‖ ≤
      ‖h‖ * ‖((ContinuousMap.toLp 2 volume ℂ) q) t -
        measurableUnitFunctionL2 u hu hunit t‖
  rw [hqmul, humul, hqcoe, hhcoe, hucoe, ← sub_mul,
    norm_mul]
  nlinarith [ContinuousMap.norm_coe_le_norm h t,
    norm_nonneg (q t - u t)]

theorem continuous_sub_unit_multiplier_norm_le
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1)
    (q : C(SymplecticTorus, ℂ))
    (hq : ∀ t, ‖q t‖ ≤ 1) (f : TorusL2)
    (h : C(SymplecticTorus, ℂ)) :
    ‖continuousTorusMultiplier q f -
        l2UnitModulusMultiplierEquiv u hu hunit f‖ ≤
      2 * ‖f - (ContinuousMap.toLp 2 volume ℂ) h‖ +
        ‖h‖ * ‖(ContinuousMap.toLp 2 volume ℂ) q -
          measurableUnitFunctionL2 u hu hunit‖ := by
  let hL2 := (ContinuousMap.toLp 2 volume ℂ) h
  have hdecomp :
      continuousTorusMultiplier q f -
          l2UnitModulusMultiplierEquiv u hu hunit f =
        (continuousTorusMultiplier q (f - hL2) -
          l2UnitModulusMultiplierEquiv u hu hunit (f - hL2)) +
        (continuousTorusMultiplier q hL2 -
          l2UnitModulusMultiplierEquiv u hu hunit hL2) := by
    simp only [map_sub, hL2]
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans <| add_le_add
    (continuous_sub_unit_multiplier_norm_le_two
      u hu hunit q hq (f - hL2))
    (continuous_sub_unit_multiplier_on_continuous_norm_le
      u hu hunit q h)

theorem exists_continuous_multiplier_approx
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1)
    (f : TorusL2) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : C(SymplecticTorus, ℂ),
      (∀ t, ‖q t‖ ≤ 1) ∧
      ‖continuousTorusMultiplier q f -
          l2UnitModulusMultiplierEquiv u hu hunit f‖ < ε := by
  obtain ⟨h, hh⟩ :=
    (ContinuousMap.toLp_denseRange ℂ volume ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).exists_dist_lt
      f (by positivity : 0 < ε / 8)
  let δ : ℝ := ε / (4 * (‖h‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨q, hqbound, hq⟩ :=
    exists_continuous_norm_le_one_approx u hu hunit hδ
  refine ⟨q, hqbound, ?_⟩
  apply lt_of_le_of_lt
    (continuous_sub_unit_multiplier_norm_le
      u hu hunit q hqbound f h)
  rw [dist_eq_norm] at hh
  have hh' :
      ‖f - (ContinuousMap.toLp 2 volume ℂ) h‖ < ε / 8 := hh
  have hhnonneg : 0 ≤ ‖h‖ := norm_nonneg h
  have hdenpos : 0 < 4 * (‖h‖ + 1) := by positivity
  have hq' :
      ‖h‖ * ‖(ContinuousMap.toLp 2 volume ℂ) q -
          measurableUnitFunctionL2 u hu hunit‖ ≤
        ‖h‖ * δ := by
    exact mul_le_mul_of_nonneg_left hq.le hhnonneg
  have hdelta :
      ‖h‖ * δ ≤ ε / 4 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  nlinarith

theorem continuousTorusMultiplier_mFourier
    (v : IntegralLattice) :
    continuousTorusMultiplier
        (UnitAddTorus.mFourier (symplecticFourierIndex v)) =
      (latticeCharacterMultiplierEquiv v :
        TorusL2 →L[ℂ] TorusL2) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    continuousTorusMultiplier_coeFn
      (UnitAddTorus.mFourier (symplecticFourierIndex v)) f,
    latticeCharacterMultiplierEquiv_coeFn v f] with t hleft hright
  rw [hleft]
  change _ = (latticeCharacterMultiplierEquiv v f) t
  rw [hright]
  rw [← latticeCharacter_coe_eq_mFourier]

theorem continuousTorusMultiplier_mFourier'
    (n : SymplecticIndex → ℤ) :
    continuousTorusMultiplier (UnitAddTorus.mFourier n) =
      (latticeCharacterMultiplierEquiv
        (symplecticFourierIndex.symm n) :
        TorusL2 →L[ℂ] TorusL2) := by
  simpa using
    continuousTorusMultiplier_mFourier
      (symplecticFourierIndex.symm n)

theorem commute_continuousTorusMultiplier_of_commute_characters
    (T : TorusL2 →L[ℂ] TorusL2)
    (hT : ∀ v : IntegralLattice,
      Commute T
        (latticeCharacterMultiplierEquiv v :
          TorusL2 →L[ℂ] TorusL2))
    (u : C(SymplecticTorus, ℂ)) :
    Commute T (continuousTorusMultiplier u) := by
  let leftMap :
      C(SymplecticTorus, ℂ) →L[ℂ]
        (TorusL2 →L[ℂ] TorusL2) :=
    ((ContinuousLinearMap.mul ℂ
      (TorusL2 →L[ℂ] TorusL2)) T).comp
        continuousTorusMultiplier
  let rightMap :
      C(SymplecticTorus, ℂ) →L[ℂ]
        (TorusL2 →L[ℂ] TorusL2) :=
    ((ContinuousLinearMap.mul ℂ
      (TorusL2 →L[ℂ] TorusL2)).flip T).comp
        continuousTorusMultiplier
  have hdense :
      Dense (↑(Submodule.span ℂ
        (Set.range (UnitAddTorus.mFourier :
          (SymplecticIndex → ℤ) → C(SymplecticTorus, ℂ)))) :
            Set C(SymplecticTorus, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      UnitAddTorus.span_mFourier_closure_eq_top
  have heqfun : (leftMap : C(SymplecticTorus, ℂ) →
      (TorusL2 →L[ℂ] TorusL2)) = rightMap := by
    apply Continuous.ext_on hdense leftMap.continuous rightMap.continuous
    intro q hq
    refine Submodule.span_induction
      (p := fun q _ => leftMap q = rightMap q) ?_ ?_ ?_ ?_ hq
    · intro q hq
      obtain ⟨n, rfl⟩ := hq
      change T * continuousTorusMultiplier (UnitAddTorus.mFourier n) =
        continuousTorusMultiplier (UnitAddTorus.mFourier n) * T
      rw [continuousTorusMultiplier_mFourier']
      exact (hT _).eq
    · exact map_zero leftMap |>.trans (map_zero rightMap).symm
    · intro x y _ _ hx hy
      rw [map_add, map_add, hx, hy]
    · intro c x _ hx
      rw [map_smul, map_smul, hx]
  change T * continuousTorusMultiplier u =
    continuousTorusMultiplier u * T
  exact congrFun heqfun u

theorem exists_continuous_multiplier_approx_pair
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1)
    (f₁ f₂ : TorusL2) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : C(SymplecticTorus, ℂ),
      (∀ t, ‖q t‖ ≤ 1) ∧
      ‖continuousTorusMultiplier q f₁ -
          l2UnitModulusMultiplierEquiv u hu hunit f₁‖ < ε ∧
      ‖continuousTorusMultiplier q f₂ -
          l2UnitModulusMultiplierEquiv u hu hunit f₂‖ < ε := by
  obtain ⟨h₁, hh₁⟩ :=
    (ContinuousMap.toLp_denseRange ℂ volume ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).exists_dist_lt
      f₁ (by positivity : 0 < ε / 8)
  obtain ⟨h₂, hh₂⟩ :=
    (ContinuousMap.toLp_denseRange ℂ volume ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).exists_dist_lt
      f₂ (by positivity : 0 < ε / 8)
  let δ : ℝ := ε / (4 * (‖h₁‖ + ‖h₂‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨q, hqbound, hq⟩ :=
    exists_continuous_norm_le_one_approx u hu hunit hδ
  refine ⟨q, hqbound, ?_, ?_⟩
  all_goals
    apply lt_of_le_of_lt
      (continuous_sub_unit_multiplier_norm_le
        u hu hunit q hqbound _ _)
  · rw [dist_eq_norm] at hh₁
    have hmul :
        ‖h₁‖ * ‖(ContinuousMap.toLp 2 volume ℂ) q -
            measurableUnitFunctionL2 u hu hunit‖ ≤ ‖h₁‖ * δ :=
      mul_le_mul_of_nonneg_left hq.le (norm_nonneg h₁)
    have hdelta : ‖h₁‖ * δ ≤ ε / 4 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity :
        0 < 4 * (‖h₁‖ + ‖h₂‖ + 1))).2
      nlinarith [norm_nonneg h₁, norm_nonneg h₂]
    nlinarith
  · rw [dist_eq_norm] at hh₂
    have hmul :
        ‖h₂‖ * ‖(ContinuousMap.toLp 2 volume ℂ) q -
            measurableUnitFunctionL2 u hu hunit‖ ≤ ‖h₂‖ * δ :=
      mul_le_mul_of_nonneg_left hq.le (norm_nonneg h₂)
    have hdelta : ‖h₂‖ * δ ≤ ε / 4 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity :
        0 < 4 * (‖h₁‖ + ‖h₂‖ + 1))).2
      nlinarith [norm_nonneg h₁, norm_nonneg h₂]
    nlinarith

theorem commute_unitMultiplier_of_commute_characters
    (T : TorusL2 →L[ℂ] TorusL2)
    (hT : ∀ v : IntegralLattice,
      Commute T
        (latticeCharacterMultiplierEquiv v :
          TorusL2 →L[ℂ] TorusL2))
    (u : SymplecticTorus → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1) :
    Commute T
      (l2UnitModulusMultiplierEquiv (μ := volume) u hu hunit :
        TorusL2 →L[ℂ] TorusL2) := by
  change T *
      (l2UnitModulusMultiplierEquiv (μ := volume) u hu hunit :
        TorusL2 →L[ℂ] TorusL2) =
    (l2UnitModulusMultiplierEquiv (μ := volume) u hu hunit :
      TorusL2 →L[ℂ] TorusL2) * T
  apply ContinuousLinearMap.ext
  intro f
  change T (l2UnitModulusMultiplierEquiv u hu hunit f) =
    l2UnitModulusMultiplierEquiv u hu hunit (T f)
  let d : TorusL2 :=
    T (l2UnitModulusMultiplierEquiv u hu hunit f) -
      l2UnitModulusMultiplierEquiv u hu hunit (T f)
  by_contra hne
  have hdne : d ≠ 0 := by
    intro hd
    apply hne
    exact sub_eq_zero.mp hd
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  let ε : ℝ := ‖d‖ / (2 * (‖T‖ + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨q, _hqbound, hqf, hqTf⟩ :=
    exists_continuous_multiplier_approx_pair
      u hu hunit f (T f) hε
  have hcomm := commute_continuousTorusMultiplier_of_commute_characters
    T hT q
  have hcommf :
      T (continuousTorusMultiplier q f) =
        continuousTorusMultiplier q (T f) := by
    exact DFunLike.congr_fun hcomm.eq f
  have hdecomp :
      d =
        T (l2UnitModulusMultiplierEquiv u hu hunit f -
          continuousTorusMultiplier q f) +
        (continuousTorusMultiplier q (T f) -
          l2UnitModulusMultiplierEquiv u hu hunit (T f)) := by
    dsimp [d]
    rw [map_sub, hcommf]
    abel
  have hfirst :
      ‖T (l2UnitModulusMultiplierEquiv u hu hunit f -
          continuousTorusMultiplier q f)‖ ≤
        ‖T‖ * ε := by
    exact (T.le_opNorm _).trans <|
      mul_le_mul_of_nonneg_left (by
        rw [norm_sub_rev]
        exact hqf.le) (norm_nonneg T)
  have htotal :
      ‖d‖ < ‖T‖ * ε + ε := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans_lt (add_lt_add_of_le_of_lt hfirst hqTf)
  dsimp [ε] at htotal
  have hdenpos : 0 < 2 * (‖T‖ + 1) := by positivity
  have heq :
      ‖T‖ * (‖d‖ / (2 * (‖T‖ + 1))) +
          ‖d‖ / (2 * (‖T‖ + 1)) =
        ‖d‖ / 2 := by
    field_simp
  rw [heq] at htotal
  linarith

end

end ConnesRigidity

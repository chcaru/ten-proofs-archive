
import ConnesRigidity.TorusCochain
import ConnesRigidity.GroupVonNeumannAlgebra
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace ConnesRigidity

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

universe u v w

private def l2FiberMap
    {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (e : ∀ i, E i ≃ₗᵢ[ℂ] F i) (f : lp E 2) :
    PreLp F :=
  fun i => e i (f i)

private theorem l2FiberMap_mem
    {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (e : ∀ i, E i ≃ₗᵢ[ℂ] F i) (f : lp E 2) :
    l2FiberMap e f ∈ lp F 2 := by
  change Memℓp (fun i => e i (f i)) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simpa only [LinearIsometryEquiv.norm_map] using
    (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

def l2FiberwiseEquiv
    {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (e : ∀ i, E i ≃ₗᵢ[ℂ] F i) :
    lp E 2 ≃ₗᵢ[ℂ] lp F 2 where
  toLinearEquiv :=
    { toFun := fun f => ⟨l2FiberMap e f, l2FiberMap_mem e f⟩
      invFun := fun f => ⟨l2FiberMap (fun i => (e i).symm) f,
        l2FiberMap_mem (fun i => (e i).symm) f⟩
      left_inv := by
        intro f
        ext i
        exact (e i).symm_apply_apply (f i)
      right_inv := by
        intro f
        ext i
        exact (e i).apply_symm_apply (f i)
      map_add' := by
        intro f h
        ext i
        exact map_add (e i) (f i) (h i)
      map_smul' := by
        intro c f
        ext i
        exact map_smul (e i) c (f i) }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change
      (∑' i, ‖e i (f i)‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) =
        (∑' i, ‖f i‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal)
    simp only [LinearIsometryEquiv.norm_map]

@[simp]
theorem l2FiberwiseEquiv_apply
    {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (e : ∀ i, E i ≃ₗᵢ[ℂ] F i) (f : lp E 2) (i : ι) :
    l2FiberwiseEquiv e f i = e i (f i) :=
  rfl

theorem l2FiberwiseEquiv_single
    {ι : Type*} {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (e : ∀ i, E i ≃ₗᵢ[ℂ] F i) [DecidableEq ι]
    (i : ι) (x : E i) :
    l2FiberwiseEquiv e (lp.single 2 i x) =
      lp.single 2 i (e i x) := by
  ext j
  simp only [l2FiberwiseEquiv_apply, lp.single_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

private def l2CurryFiber {ι : Type u} {κ : Type v}
    (f : GroupL2 (ι × κ)) (i : ι) : GroupL2 κ :=
  ⟨fun k => f (i, k), by
    change Memℓp (fun k => f (i, k)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact ((lp.memℓp f).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).prod_factor i⟩

private theorem l2Curry_mem {ι : Type u} {κ : Type v}
    (f : GroupL2 (ι × κ)) :
    (fun i => l2CurryFiber f i) ∈ lp (fun _ : ι => GroupL2 κ) 2 := by
  change Memℓp (fun i => l2CurryFiber f i) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have hprod : Summable (fun p : ι × κ =>
      ‖f p‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply hprod.prod.congr
  intro i
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  rfl

private theorem l2Uncurry_mem {ι : Type u} {κ : Type v}
    (f : lp (fun _ : ι => GroupL2 κ) 2) :
    (fun p : ι × κ => f p.1 p.2) ∈ GroupL2 (ι × κ) := by
  change Memℓp (fun p : ι × κ => f p.1 p.2) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  apply (summable_prod_of_nonneg (fun _ => by positivity)).2
  constructor
  · intro i
    exact (lp.memℓp (f i)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  · have hout : Summable (fun i =>
        ‖f i‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp f).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    convert hout using 1
    funext i
    rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]

def l2Curry (ι : Type u) (κ : Type v) :
    GroupL2 (ι × κ) ≃ₗᵢ[ℂ] lp (fun _ : ι => GroupL2 κ) 2 where
  toLinearEquiv :=
    { toFun := fun f => ⟨fun i => l2CurryFiber f i, l2Curry_mem f⟩
      invFun := fun f => ⟨fun p => f p.1 p.2, l2Uncurry_mem f⟩
      left_inv := by
        intro f
        ext p
        rfl
      right_inv := by
        intro f
        ext i k
        rfl
      map_add' := by
        intro f h
        ext i k
        rfl
      map_smul' := by
        intro c f
        ext i k
        rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change
      (∑' i, ‖l2CurryFiber f i‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) =
        (∑' p, ‖f p‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal)
    congr 1
    have hprod : Summable (fun p : ι × κ =>
        ‖f p‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    rw [hprod.tsum_prod]
    apply tsum_congr
    intro i
    rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rfl

@[simp]
theorem l2Curry_apply {ι : Type u} {κ : Type v}
    (f : GroupL2 (ι × κ)) (i : ι) (k : κ) :
    l2Curry ι κ f i k = f (i, k) :=
  rfl

@[simp]
theorem l2Curry_symm_apply {ι : Type u} {κ : Type v}
    (f : lp (fun _ : ι => GroupL2 κ) 2) (i : ι) (k : κ) :
    (l2Curry ι κ).symm f (i, k) = f i k :=
  rfl

private def l2IndexReindexFun {ι : Type u} {κ : Type v}
    {E : Type*} [NormedAddCommGroup E] (e : ι ≃ κ)
    (f : lp (fun _ : ι => E) 2) : PreLp (fun _ : κ => E) :=
  fun k => f (e.symm k)

private theorem l2IndexReindexFun_mem {ι : Type u} {κ : Type v}
    {E : Type*} [NormedAddCommGroup E] (e : ι ≃ κ)
    (f : lp (fun _ : ι => E) 2) :
    l2IndexReindexFun e f ∈ lp (fun _ : κ => E) 2 := by
  change Memℓp (fun k : κ => f (e.symm k)) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  exact (e.symm.summable_iff).2
    ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))

def l2IndexReindex {ι : Type u} {κ : Type v}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : ι ≃ κ) :
    lp (fun _ : ι => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : κ => E) 2 where
  toLinearEquiv :=
    { toFun := fun f => ⟨l2IndexReindexFun e f, l2IndexReindexFun_mem e f⟩
      invFun := fun f =>
        ⟨l2IndexReindexFun e.symm f, l2IndexReindexFun_mem e.symm f⟩
      left_inv := by
        intro f
        ext i
        simp [l2IndexReindexFun]
      right_inv := by
        intro f
        ext k
        simp [l2IndexReindexFun]
      map_add' := by
        intro f h
        ext k
        rfl
      map_smul' := by
        intro c f
        ext k
        rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change
      (∑' k : κ, ‖f (e.symm k)‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) =
        (∑' i : ι, ‖f i‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal)
    congr 1
    exact e.symm.tsum_eq
      (fun i : ι => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp]
theorem l2IndexReindex_apply {ι : Type u} {κ : Type v}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : ι ≃ κ) (f : lp (fun _ : ι => E) 2) (k : κ) :
    l2IndexReindex e f k = f (e.symm k) :=
  rfl

theorem l2IndexReindex_single {ι : Type u} {κ : Type v}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : ι ≃ κ) [DecidableEq ι] [DecidableEq κ]
    (i : ι) (x : E) :
    l2IndexReindex e (lp.single 2 i x) = lp.single 2 (e i) x := by
  ext k
  simp only [l2IndexReindex_apply, lp.single_apply]
  by_cases h : e.symm k = i
  · have hk : k = e i := by simpa using congrArg e h
    simp [hk]
  · have hk : k ≠ e i := by
      intro hk
      apply h
      simp [hk]
    simp [h, hk]

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

private theorem unitModulus_memLpTop (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) :
    MemLp u ∞ μ := by
  apply memLp_top_of_bound hu.aestronglyMeasurable 1
  filter_upwards
  intro x
  rw [hunit]

private theorem unitModulusMultiplierMemLp (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) (f : Lp ℂ 2 μ) :
    MemLp (fun x => u x * f x) 2 μ :=
  (Lp.memLp f).mul' (unitModulus_memLpTop u hu hunit)

def l2UnitModulusMultiplier (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (unitModulusMultiplierMemLp u hu hunit f).toLp
    (fun x => u x * f x)

theorem l2UnitModulusMultiplier_coeFn (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) (f : Lp ℂ 2 μ) :
    l2UnitModulusMultiplier u hu hunit f =ᵐ[μ] fun x => u x * f x :=
  (unitModulusMultiplierMemLp u hu hunit f).coeFn_toLp

theorem l2UnitModulusMultiplier_add (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) (f h : Lp ℂ 2 μ) :
    l2UnitModulusMultiplier u hu hunit (f + h) =
      l2UnitModulusMultiplier u hu hunit f +
        l2UnitModulusMultiplier u hu hunit h := by
  apply Lp.ext
  filter_upwards [
    l2UnitModulusMultiplier_coeFn u hu hunit (f + h),
    l2UnitModulusMultiplier_coeFn u hu hunit f,
    l2UnitModulusMultiplier_coeFn u hu hunit h,
    Lp.coeFn_add f h,
    Lp.coeFn_add (l2UnitModulusMultiplier u hu hunit f)
      (l2UnitModulusMultiplier u hu hunit h)] with x hleft hf hh hin hout
  calc
    _ = u x * (f x + h x) := by rw [hleft, hin]; rfl
    _ = u x * f x + u x * h x := mul_add _ _ _
    _ = _ := by rw [← hf, ← hh]; exact hout.symm

theorem l2UnitModulusMultiplier_smul (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) (c : ℂ) (f : Lp ℂ 2 μ) :
    l2UnitModulusMultiplier u hu hunit (c • f) =
      c • l2UnitModulusMultiplier u hu hunit f := by
  apply Lp.ext
  filter_upwards [
    l2UnitModulusMultiplier_coeFn u hu hunit (c • f),
    l2UnitModulusMultiplier_coeFn u hu hunit f,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c (l2UnitModulusMultiplier u hu hunit f)] with x hleft hf hin hout
  calc
    _ = u x * (c * f x) := by rw [hleft, hin]; rfl
    _ = c * (u x * f x) := by ring
    _ = _ := by rw [← hf]; exact hout.symm

theorem l2UnitModulusMultiplier_norm (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) (f : Lp ℂ 2 μ) :
    ‖l2UnitModulusMultiplier u hu hunit f‖ = ‖f‖ := by
  rw [l2UnitModulusMultiplier, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards
  intro x
  rw [norm_mul, hunit, one_mul]

private theorem measurable_conj_comp (u : α → ℂ) (hu : Measurable u) :
    Measurable (fun x => conj (u x)) :=
  Complex.continuous_conj.measurable.comp hu

omit [MeasurableSpace α] in
private theorem norm_conj_comp (u : α → ℂ) (hunit : ∀ x, ‖u x‖ = 1) :
    ∀ x, ‖conj (u x)‖ = 1 := by
  intro x
  rw [Complex.norm_conj, hunit]

def l2UnitModulusMultiplierEquiv (u : α → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { toFun := l2UnitModulusMultiplier u hu hunit
      invFun := l2UnitModulusMultiplier (fun x => conj (u x))
        (measurable_conj_comp u hu) (norm_conj_comp u hunit)
      left_inv := by
        intro f
        apply Lp.ext
        filter_upwards [
          l2UnitModulusMultiplier_coeFn u hu hunit f,
          l2UnitModulusMultiplier_coeFn (fun x => conj (u x))
            (measurable_conj_comp u hu) (norm_conj_comp u hunit)
            (l2UnitModulusMultiplier u hu hunit f)] with x hin hout
        calc
          _ = conj (u x) * (u x * f x) := by rw [hout, hin]
          _ = f x := by
            rw [← mul_assoc, Complex.conj_mul', hunit]
            norm_num
      right_inv := by
        intro f
        apply Lp.ext
        filter_upwards [
          l2UnitModulusMultiplier_coeFn (fun x => conj (u x))
            (measurable_conj_comp u hu) (norm_conj_comp u hunit) f,
          l2UnitModulusMultiplier_coeFn u hu hunit
            (l2UnitModulusMultiplier (fun x => conj (u x))
              (measurable_conj_comp u hu) (norm_conj_comp u hunit) f)] with x hin hout
        calc
          _ = u x * (conj (u x) * f x) := by rw [hout, hin]
          _ = f x := by
            rw [← mul_assoc, Complex.mul_conj', hunit]
            norm_num
      map_add' := l2UnitModulusMultiplier_add u hu hunit
      map_smul' := l2UnitModulusMultiplier_smul u hu hunit }
  norm_map' := l2UnitModulusMultiplier_norm u hu hunit

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusActionAddEquiv (g : IntegralSymplecticGroup) :
    SymplecticTorus ≃+ SymplecticTorus where
  toFun t := g • t
  invFun t := g⁻¹ • t
  left_inv t := by simp
  right_inv t := by simp
  map_add' x y := smul_add g x y

theorem torusAction_measurePreserving (g : IntegralSymplecticGroup) :
    MeasurePreserving (fun t : SymplecticTorus => g • t) volume volume := by
  have hg : Measurable (fun t : SymplecticTorus => g • t) :=
    (continuous_torus_smul g).measurable
  let μg : Measure SymplecticTorus :=
    Measure.map (torusActionAddEquiv g) volume
  haveI hprob : IsProbabilityMeasure μg :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  haveI hhaar : Measure.IsAddHaarMeasure μg :=
    AddEquiv.isAddHaarMeasure_map volume (torusActionAddEquiv g)
      (continuous_torus_smul g) (continuous_torus_smul g⁻¹)
  refine ⟨hg, ?_⟩
  change μg = volume
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure μg volume

abbrev TorusL2 :=
  Lp ℂ 2 (volume : Measure SymplecticTorus)

abbrev CrossedHilbert :=
  lp (fun _ : IntegralSymplecticGroup => TorusL2) 2

def torusActionL2Equiv (g : IntegralSymplecticGroup) :
    TorusL2 ≃ₗᵢ[ℂ] TorusL2 where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving (fun t : SymplecticTorus => g • t)
        (torusAction_measurePreserving g)
      invFun := Lp.compMeasurePreserving (fun t : SymplecticTorus => g⁻¹ • t)
        (torusAction_measurePreserving g⁻¹)
      left_inv := by
        intro f
        apply Lp.ext
        have hin := Lp.coeFn_compMeasurePreserving f
          (torusAction_measurePreserving g)
        have hin' :=
          (torusAction_measurePreserving g⁻¹).quasiMeasurePreserving.ae_eq_comp hin
        filter_upwards [
          Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreserving (fun t : SymplecticTorus => g • t)
              (torusAction_measurePreserving g) f)
            (torusAction_measurePreserving g⁻¹),
          hin'] with t hout hin'
        rw [hout]
        exact hin'.trans (by simp)
      right_inv := by
        intro f
        apply Lp.ext
        have hin := Lp.coeFn_compMeasurePreserving f
          (torusAction_measurePreserving g⁻¹)
        have hin' :=
          (torusAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp hin
        filter_upwards [
          Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreserving (fun t : SymplecticTorus => g⁻¹ • t)
              (torusAction_measurePreserving g⁻¹) f)
            (torusAction_measurePreserving g),
          hin'] with t hout hin'
        rw [hout]
        exact hin'.trans (by simp)
      map_add' := by
        intro f h
        exact map_add
          (Lp.compMeasurePreserving (fun t : SymplecticTorus => g • t)
            (torusAction_measurePreserving g)) f h
      map_smul' := by
        intro c f
        exact map_smul
          (Lp.compMeasurePreservingₗ ℂ (fun t : SymplecticTorus => g • t)
            (torusAction_measurePreserving g)) c f }
  norm_map' := fun f =>
    Lp.norm_compMeasurePreserving f (torusAction_measurePreserving g)

theorem torusActionL2Equiv_coeFn (g : IntegralSymplecticGroup)
    (f : TorusL2) :
    torusActionL2Equiv g f =ᵐ[volume]
      fun t : SymplecticTorus => f (g • t) :=
  Lp.coeFn_compMeasurePreserving f (torusAction_measurePreserving g)

private theorem latticeCharacter_complex_norm (v : IntegralLattice) :
    ∀ t, ‖(latticeCharacter v t : ℂ)‖ = 1 :=
  fun t => Circle.norm_coe (latticeCharacter v t)

def latticeCharacterMultiplierEquiv (v : IntegralLattice) :
    TorusL2 ≃ₗᵢ[ℂ] TorusL2 :=
  l2UnitModulusMultiplierEquiv
    (fun t => (latticeCharacter v t : ℂ))
    (measurable_latticeCharacter_complex v)
    (latticeCharacter_complex_norm v)

theorem torusActionL2Equiv_latticeFourier
    (g : IntegralSymplecticGroup) (v : IntegralLattice) :
    torusActionL2Equiv g⁻¹
        (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex v)) =
      UnitAddTorus.mFourierLp 2
        (symplecticFourierIndex (g • v)) := by
  apply Lp.ext
  have hin :=
    UnitAddTorus.coeFn_mFourierLp 2 (symplecticFourierIndex v)
  have hin' :=
    (torusAction_measurePreserving g⁻¹).quasiMeasurePreserving.ae_eq_comp hin
  filter_upwards [
    torusActionL2Equiv_coeFn g⁻¹
      (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex v)),
    hin',
    UnitAddTorus.coeFn_mFourierLp 2
      (symplecticFourierIndex (g • v))] with t hact hin hout
  have hin_eval :
      (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex v) :
          SymplecticTorus → ℂ) (g⁻¹ • t) =
        UnitAddTorus.mFourier (symplecticFourierIndex v) (g⁻¹ • t) := by
    simpa only [Function.comp_apply] using hin
  rw [hact, hin_eval, hout]
  rw [← latticeCharacter_coe_eq_mFourier,
    ← latticeCharacter_coe_eq_mFourier]
  exact congrArg ((↑) : Circle → ℂ) (latticeCharacter_action g v t).symm

theorem latticeCharacterMultiplierEquiv_coeFn
    (v : IntegralLattice) (f : TorusL2) :
    latticeCharacterMultiplierEquiv v f =ᵐ[volume]
      fun t => (latticeCharacter v t : ℂ) * f t :=
  l2UnitModulusMultiplier_coeFn
    (fun t => (latticeCharacter v t : ℂ))
    (measurable_latticeCharacter_complex v)
    (fun t => Circle.norm_coe (latticeCharacter v t)) f

theorem latticeCharacterMultiplierEquiv_latticeFourier
    (v w : IntegralLattice) :
    latticeCharacterMultiplierEquiv v
        (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex w)) =
      UnitAddTorus.mFourierLp 2
        (symplecticFourierIndex (v + w)) := by
  apply Lp.ext
  filter_upwards [
    latticeCharacterMultiplierEquiv_coeFn v
      (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex w)),
    UnitAddTorus.coeFn_mFourierLp 2 (symplecticFourierIndex w),
    UnitAddTorus.coeFn_mFourierLp 2
      (symplecticFourierIndex (v + w))] with t hmul hin hout
  rw [hmul, hin, hout]
  rw [← latticeCharacter_coe_eq_mFourier w t]
  rw [← latticeCharacter_coe_eq_mFourier (v + w) t]
  simpa only [Circle.coe_mul] using
    congrArg ((↑) : Circle → ℂ) (latticeCharacter_add v w t).symm

def crossedTorusActionEquiv (g : IntegralSymplecticGroup) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  l2FiberwiseEquiv (fun _ => torusActionL2Equiv g⁻¹)

def crossedOuterTranslationEquiv (g : IntegralSymplecticGroup) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  l2IndexReindex (Equiv.mulLeft g)

def crossedCharacterMultiplierEquiv
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    (x : CocycleExtension c) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  l2FiberwiseEquiv (fun q =>
    latticeCharacterMultiplierEquiv
      (x.fst + c x.snd (x.snd⁻¹ * q)))

def explicitCrossedRegularEquiv
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    (x : CocycleExtension c) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  (crossedTorusActionEquiv x.snd).trans <|
    (crossedOuterTranslationEquiv x.snd).trans <|
      crossedCharacterMultiplierEquiv c x

theorem explicitCrossedRegularEquiv_single
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    (x : CocycleExtension c) (k : IntegralSymplecticGroup)
    (f : TorusL2) :
    explicitCrossedRegularEquiv c x (lp.single 2 k f) =
      lp.single 2 (x.snd * k)
        (latticeCharacterMultiplierEquiv
          (x.fst + c x.snd k) (torusActionL2Equiv x.snd⁻¹ f)) := by
  rw [explicitCrossedRegularEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, crossedTorusActionEquiv,
    l2FiberwiseEquiv_single, crossedOuterTranslationEquiv,
    l2IndexReindex_single, crossedCharacterMultiplierEquiv,
    l2FiberwiseEquiv_single]
  simp

def cocycleExtensionCoordinates
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice) :
    CocycleExtension c ≃ IntegralSymplecticGroup × IntegralLattice where
  toFun x := (x.snd, x.fst)
  invFun x := ⟨x.2, x.1⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

def latticeFourierEquiv :
    GroupL2 IntegralLattice ≃ₗᵢ[ℂ] TorusL2 :=
  (l2Reindex symplecticFourierIndex.toEquiv).trans
    (UnitAddTorus.mFourierBasis (d := SymplecticIndex)).repr.symm

def extensionPartialFourier
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice) :
    GroupL2 (CocycleExtension c) ≃ₗᵢ[ℂ] CrossedHilbert :=
  (l2Reindex (cocycleExtensionCoordinates c)).trans <|
    (l2Curry IntegralSymplecticGroup IntegralLattice).trans <|
      l2FiberwiseEquiv (fun _ => latticeFourierEquiv)

private theorem torusCochain_complex_norm
    (g : IntegralSymplecticGroup) :
    ∀ t, ‖(torusCochain g t : ℂ)‖ = 1 := by
  intro t
  exact Circle.norm_coe _

private theorem torusCochain_conj_measurable
    (g : IntegralSymplecticGroup) :
    Measurable (fun t => conj (torusCochain g t : ℂ)) :=
  Complex.continuous_conj.measurable.comp
    (measurable_torusCochain_complex g)

private theorem torusCochain_conj_norm
    (g : IntegralSymplecticGroup) :
    ∀ t, ‖conj (torusCochain g t : ℂ)‖ = 1 := by
  intro t
  rw [Complex.norm_conj]
  exact Circle.norm_coe _

def torusCochainInverseMultiplierEquiv
    (g : IntegralSymplecticGroup) :
    TorusL2 ≃ₗᵢ[ℂ] TorusL2 :=
  l2UnitModulusMultiplierEquiv
    (fun t => conj (torusCochain g t : ℂ))
    (torusCochain_conj_measurable g)
    (torusCochain_conj_norm g)

def torusCochainDiagonalEquiv :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  l2FiberwiseEquiv torusCochainInverseMultiplierEquiv

theorem l2Reindex_single
    {α β : Type*} (e : α ≃ β) [DecidableEq α] [DecidableEq β]
    (i : α) (z : ℂ) :
    l2Reindex e (lp.single 2 i z) = lp.single 2 (e i) z := by
  ext j
  simp only [l2Reindex_apply, lp.single_apply]
  by_cases h : e.symm j = i
  · have hj : j = e i := by
      simpa using congrArg e h
    simp [hj]
  · have hj : j ≠ e i := by
      intro hj
      apply h
      simp [hj]
    simp [h, hj]

theorem l2Curry_single
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (i : ι) (k : κ) (z : ℂ) :
    l2Curry ι κ (lp.single 2 (i, k) z) =
      lp.single 2 i (lp.single 2 k z) := by
  ext j l
  simp only [l2Curry_apply, lp.single_apply]
  by_cases hi : i = j
  · subst j
    by_cases hk : k = l
    · subst l
      simp
    · simp [hk]
  · have hp : (i, k) ≠ (j, l) := by
      intro h
      exact hi (congrArg Prod.fst h)
    simp [hi, hp]

theorem extensionPartialFourier_single
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    [DecidableEq (CocycleExtension c)]
    (x : CocycleExtension c) :
    extensionPartialFourier c (lp.single 2 x 1) =
      lp.single 2 x.snd
        (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex x.fst)) := by
  rw [extensionPartialFourier, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, l2Reindex_single, l2Curry_single,
    l2FiberwiseEquiv_single, latticeFourierEquiv,
    LinearIsometryEquiv.trans_apply, l2Reindex_single]
  rw [HilbertBasis.repr_symm_single]
  simp only [UnitAddTorus.coe_mFourierBasis]
  rfl

theorem leftRegularUnitary_single
    {G : Type*} [Group G] [DecidableEq G] (g h : G) (z : ℂ) :
    (leftRegularUnitary g : GroupL2 G →L[ℂ] GroupL2 G)
        (lp.single 2 h z) =
      lp.single 2 (g * h) z := by
  ext k
  simp only [leftRegularUnitary_apply, lp.single_apply]
  by_cases hk : g⁻¹ * k = h
  · have hk' : k = g * h := by
      calc
        k = g * (g⁻¹ * k) := by simp
        _ = g * h := by rw [hk]
    simp [hk']
  · have hk' : k ≠ g * h := by
      intro hk'
      apply hk
      simp [hk']
    simp [hk, hk']

theorem extensionPartialFourier_leftRegular_single
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    [DecidableEq (CocycleExtension c)]
    (x y : CocycleExtension c) :
    extensionPartialFourier c
        ((leftRegularUnitary x :
          GroupL2 (CocycleExtension c) →L[ℂ] GroupL2 (CocycleExtension c))
          (lp.single 2 y 1)) =
      lp.single 2 (x.snd * y.snd)
        (UnitAddTorus.mFourierLp 2
          (symplecticFourierIndex
            (x.fst + x.snd • y.fst + c x.snd y.snd))) := by
  rw [leftRegularUnitary_single, extensionPartialFourier_single]
  rfl

theorem torusCochainDiagonalEquiv_single
    (g : IntegralSymplecticGroup) (v : IntegralLattice) :
    torusCochainDiagonalEquiv
        (lp.single 2 g
          (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex v))) =
      lp.single 2 g
        (torusCochainInverseMultiplierEquiv g
          (UnitAddTorus.mFourierLp 2 (symplecticFourierIndex v))) :=
  l2FiberwiseEquiv_single _ _ _

def transportedRegularEquiv
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    (x : CocycleExtension c) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  (extensionPartialFourier c).symm.trans <|
    (Unitary.linearIsometryEquiv (leftRegularUnitary x)).trans <|
      extensionPartialFourier c

private theorem transportedEquiv_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (u : E ≃ₗᵢ[ℂ] E) (ξ : E) :
    (e.symm.trans (u.trans e)) (e ξ) = e (u ξ) := by
  rw [LinearIsometryEquiv.trans_apply, e.symm_apply_apply,
    LinearIsometryEquiv.trans_apply]

theorem explicitCrossedRegularEquiv_extensionPartialFourier_single
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    [DecidableEq (CocycleExtension c)]
    (x y : CocycleExtension c) :
    explicitCrossedRegularEquiv c x
        (extensionPartialFourier c (lp.single 2 y 1)) =
      extensionPartialFourier c
        ((leftRegularUnitary x :
          GroupL2 (CocycleExtension c) →L[ℂ] GroupL2 (CocycleExtension c))
          (lp.single 2 y 1)) := by
  rw [extensionPartialFourier_single c y]
  rw [explicitCrossedRegularEquiv_single c x y.snd]
  rw [torusActionL2Equiv_latticeFourier x.snd y.fst]
  rw [extensionPartialFourier_leftRegular_single c x y]
  congr 1
  calc
    latticeCharacterMultiplierEquiv (x.fst + c x.snd y.snd)
        (UnitAddTorus.mFourierLp 2
          (symplecticFourierIndex (x.snd • y.fst))) =
        UnitAddTorus.mFourierLp 2
          (symplecticFourierIndex
            ((x.fst + c x.snd y.snd) + x.snd • y.fst)) :=
      latticeCharacterMultiplierEquiv_latticeFourier _ _
    _ = UnitAddTorus.mFourierLp 2
          (symplecticFourierIndex
            (x.fst + x.snd • y.fst + c x.snd y.snd)) := by
      congr 2
      abel

theorem transportedRegularEquiv_eq_explicitCrossedRegularEquiv
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
    (x : CocycleExtension c) :
    transportedRegularEquiv c x = explicitCrossedRegularEquiv c x := by
  classical
  apply LinearIsometryEquiv.ext
  intro ξ
  obtain ⟨η, rfl⟩ := (extensionPartialFourier c).surjective ξ
  let A : GroupL2 (CocycleExtension c) →L[ℂ] CrossedHilbert :=
    (extensionPartialFourier c).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (leftRegularUnitary x :
        GroupL2 (CocycleExtension c) →L[ℂ] GroupL2 (CocycleExtension c))
  let B : GroupL2 (CocycleExtension c) →L[ℂ] CrossedHilbert :=
    (explicitCrossedRegularEquiv c x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (extensionPartialFourier c).toContinuousLinearEquiv.toContinuousLinearMap
  have hAB : A = B := by
    refine lp.ext_continuousLinearMap
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) fun y => ?_
    apply ContinuousLinearMap.ext
    intro z
    have hsingle :
        lp.single 2 y z =
          z • (lp.single 2 y 1 :
            GroupL2 (CocycleExtension c)) := by
      ext q
      by_cases hq : y = q
      · subst q
        simp
      · simp [hq]
    change A (lp.single 2 y z) = B (lp.single 2 y z)
    rw [hsingle, map_smul, map_smul]
    apply congrArg (fun w => z • w)
    exact
      (explicitCrossedRegularEquiv_extensionPartialFourier_single c x y).symm
  rw [transportedRegularEquiv, transportedEquiv_apply]
  change A η = B η
  exact DFunLike.congr_fun hAB η

def torusCochainMultiplierEquiv
    (g : IntegralSymplecticGroup) :
    TorusL2 ≃ₗᵢ[ℂ] TorusL2 :=
  l2UnitModulusMultiplierEquiv
    (fun t => (torusCochain g t : ℂ))
    (measurable_torusCochain_complex g)
    (torusCochain_complex_norm g)

theorem torusCochainMultiplierEquiv_coeFn
    (g : IntegralSymplecticGroup) (f : TorusL2) :
    torusCochainMultiplierEquiv g f =ᵐ[volume]
      fun t => (torusCochain g t : ℂ) * f t :=
  l2UnitModulusMultiplier_coeFn
    (fun t => (torusCochain g t : ℂ))
    (measurable_torusCochain_complex g)
    (torusCochain_complex_norm g) f

theorem torusCochainInverseMultiplierEquiv_coeFn
    (g : IntegralSymplecticGroup) (f : TorusL2) :
    torusCochainInverseMultiplierEquiv g f =ᵐ[volume]
      fun t => conj (torusCochain g t : ℂ) * f t :=
  l2UnitModulusMultiplier_coeFn
    (fun t => conj (torusCochain g t : ℂ))
    (torusCochain_conj_measurable g)
    (torusCochain_conj_norm g) f

theorem torusCochainInverseMultiplierEquiv_symm_eq
    (g : IntegralSymplecticGroup) :
    (torusCochainInverseMultiplierEquiv g).symm =
      torusCochainMultiplierEquiv g := by
  apply LinearIsometryEquiv.ext
  intro f
  apply (torusCochainInverseMultiplierEquiv g).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [
    torusCochainInverseMultiplierEquiv_coeFn g
      (torusCochainMultiplierEquiv g f),
    torusCochainMultiplierEquiv_coeFn g f] with t hout hin
  rw [hout, hin]
  rw [← mul_assoc, Complex.conj_mul', torusCochain_complex_norm]
  norm_num

theorem cochain_intertwining_scalar
    (a : IntegralLattice) (g k : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    conj (torusCochain (g * k) t : ℂ) *
          (latticeCharacter a t : ℂ) *
          (torusCochain k (g⁻¹ • t) : ℂ) =
      conj (torusCochain g t : ℂ) *
        (latticeCharacter
          (a + integralSymplecticCocycleInput.twoCocycle g k) t : ℂ) := by
  have hc := torusCochain_coboundary g k t
  have ha := latticeCharacter_add a
    (integralSymplecticCocycleInput.twoCocycle g k) t
  have hcircle :
      (torusCochain (g * k) t)⁻¹ * latticeCharacter a t *
            torusCochain k (g⁻¹ • t) =
        (torusCochain g t)⁻¹ *
          latticeCharacter
            (a + integralSymplecticCocycleInput.twoCocycle g k) t := by
    rw [ha, ← hc]
    calc
      _ = latticeCharacter a t * torusCochain k (g⁻¹ • t) *
          (torusCochain (g * k) t)⁻¹ := by ac_rfl
      _ = ((torusCochain g t)⁻¹ * torusCochain g t) *
          latticeCharacter a t * torusCochain k (g⁻¹ • t) *
          (torusCochain (g * k) t)⁻¹ := by
            rw [inv_mul_cancel, one_mul]
      _ = _ := by ac_rfl
  simpa only [Circle.coe_mul, Circle.coe_inv_eq_conj] using
    congrArg ((↑) : Circle → ℂ) hcircle

theorem cochain_intertwining_fiber
    (a : IntegralLattice) (g k : IntegralSymplecticGroup)
    (f : TorusL2) :
    torusCochainInverseMultiplierEquiv (g * k)
        (latticeCharacterMultiplierEquiv a
          (torusActionL2Equiv g⁻¹
            (torusCochainMultiplierEquiv k f))) =
      torusCochainInverseMultiplierEquiv g
        (latticeCharacterMultiplierEquiv
          (a + integralSymplecticCocycleInput.twoCocycle g k)
          (torusActionL2Equiv g⁻¹ f)) := by
  apply Lp.ext
  have hk :=
    torusCochainMultiplierEquiv_coeFn k f
  have hk' :=
    (torusAction_measurePreserving g⁻¹).quasiMeasurePreserving.ae_eq_comp hk
  filter_upwards [
    torusCochainInverseMultiplierEquiv_coeFn (g * k)
      (latticeCharacterMultiplierEquiv a
        (torusActionL2Equiv g⁻¹
          (torusCochainMultiplierEquiv k f))),
    latticeCharacterMultiplierEquiv_coeFn a
      (torusActionL2Equiv g⁻¹
        (torusCochainMultiplierEquiv k f)),
    torusActionL2Equiv_coeFn g⁻¹
      (torusCochainMultiplierEquiv k f),
    hk',
    torusCochainInverseMultiplierEquiv_coeFn g
      (latticeCharacterMultiplierEquiv
        (a + integralSymplecticCocycleInput.twoCocycle g k)
        (torusActionL2Equiv g⁻¹ f)),
    latticeCharacterMultiplierEquiv_coeFn
      (a + integralSymplecticCocycleInput.twoCocycle g k)
      (torusActionL2Equiv g⁻¹ f),
    torusActionL2Equiv_coeFn g⁻¹ f
    ] with t hDout hcharout hactout hk' hDin hcharin hactin
  have hk_eval :
      (torusCochainMultiplierEquiv k f : SymplecticTorus → ℂ)
          (g⁻¹ • t) =
        (torusCochain k (g⁻¹ • t) : ℂ) * f (g⁻¹ • t) := by
    simpa only [Function.comp_apply] using hk'
  rw [hDout, hcharout, hactout, hk_eval,
    hDin, hcharin, hactin]
  rw [← mul_assoc, ← mul_assoc]
  rw [cochain_intertwining_scalar a g k t]
  rw [mul_assoc]

def crossedCochainScalarEquiv
    (g : IntegralSymplecticGroup) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  l2FiberwiseEquiv (fun _ => torusCochainInverseMultiplierEquiv g)

theorem torusCochainDiagonalEquiv_single'
    (k : IntegralSymplecticGroup) (f : TorusL2) :
    torusCochainDiagonalEquiv (lp.single 2 k f) =
      lp.single 2 k (torusCochainInverseMultiplierEquiv k f) :=
  l2FiberwiseEquiv_single _ _ _

theorem torusCochainDiagonalEquiv_symm_single
    (k : IntegralSymplecticGroup) (f : TorusL2) :
    torusCochainDiagonalEquiv.symm (lp.single 2 k f) =
      lp.single 2 k (torusCochainMultiplierEquiv k f) := by
  apply Subtype.ext
  funext q
  change (torusCochainInverseMultiplierEquiv q).symm
      ((lp.single 2 k f : CrossedHilbert) q) =
    (lp.single 2 k (torusCochainMultiplierEquiv k f) :
      CrossedHilbert) q
  simp only [lp.single_apply]
  by_cases hkq : k = q
  · subst q
    simp [torusCochainInverseMultiplierEquiv_symm_eq]
  · simp [hkq]

theorem crossedCochainScalarEquiv_single
    (g k : IntegralSymplecticGroup) (f : TorusL2) :
    crossedCochainScalarEquiv g (lp.single 2 k f) =
      lp.single 2 k (torusCochainInverseMultiplierEquiv g f) :=
  l2FiberwiseEquiv_single _ _ _

def zeroExtensionElement (a : IntegralLattice)
    (g : IntegralSymplecticGroup) :
    CocycleExtension
      (NormalizedAddCocycle.zero :
        NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice) :=
  ⟨a, g⟩

def twistedExtensionElement (a : IntegralLattice)
    (g : IntegralSymplecticGroup) :
    CocycleExtension integralSymplecticCocycleInput.twoCocycle :=
  ⟨a, g⟩

def diagonalConjugatedZeroRegularEquiv
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  torusCochainDiagonalEquiv.symm.trans
    ((explicitCrossedRegularEquiv
      (NormalizedAddCocycle.zero :
        NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice)
      (zeroExtensionElement a g)).trans
      torusCochainDiagonalEquiv)

def cochainCorrectedTwistedRegularEquiv
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  (explicitCrossedRegularEquiv
    integralSymplecticCocycleInput.twoCocycle
    (twistedExtensionElement a g)).trans
    (crossedCochainScalarEquiv g)

theorem torusCochainDiagonal_conjugates_regular_single
    (a : IntegralLattice) (g k : IntegralSymplecticGroup)
    (f : TorusL2) :
    diagonalConjugatedZeroRegularEquiv a g (lp.single 2 k f) =
      cochainCorrectedTwistedRegularEquiv a g (lp.single 2 k f) := by
  rw [diagonalConjugatedZeroRegularEquiv,
    cochainCorrectedTwistedRegularEquiv,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply,
    torusCochainDiagonalEquiv_symm_single]
  rw [explicitCrossedRegularEquiv_single]
  rw [torusCochainDiagonalEquiv_single']
  rw [LinearIsometryEquiv.trans_apply]
  rw [explicitCrossedRegularEquiv_single]
  rw [crossedCochainScalarEquiv_single]
  simp only [zeroExtensionElement, twistedExtensionElement,
    NormalizedAddCocycle.zero_apply, add_zero]
  change (lp.single 2 (g * k)
      (torusCochainInverseMultiplierEquiv (g * k)
        (latticeCharacterMultiplierEquiv a
          (torusActionL2Equiv g⁻¹
            (torusCochainMultiplierEquiv k f)))) : CrossedHilbert) =
    (lp.single 2 (g * k)
      (torusCochainInverseMultiplierEquiv g
        (latticeCharacterMultiplierEquiv
          (a + integralSymplecticCocycleInput.twoCocycle g k)
          (torusActionL2Equiv g⁻¹ f))) : CrossedHilbert)
  exact congrArg
    (fun h : TorusL2 => (lp.single 2 (g * k) h : CrossedHilbert))
    (cochain_intertwining_fiber a g k f)

theorem torusCochainDiagonal_conjugates_regular
    (a : IntegralLattice) (g : IntegralSymplecticGroup) :
    diagonalConjugatedZeroRegularEquiv a g =
      cochainCorrectedTwistedRegularEquiv a g := by
  apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
  apply ContinuousLinearEquiv.coe_injective
  refine lp.ext_continuousLinearMap
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) fun k => ?_
  apply ContinuousLinearMap.ext
  intro f
  exact torusCochainDiagonal_conjugates_regular_single a g k f

end

end ConnesRigidity

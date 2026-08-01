
import ConnesRigidity.PropertyT
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace ConnesRigidity

universe u

open scoped InnerProductSpace

abbrev RationalGroupRing (G : Type u) [Group G] :=
  MonoidAlgebra ℚ G

variable {G H : Type u} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def representationOperatorMonoidHom
    (π : UnitaryRepresentation G H) :
    G →* (H →L[ℂ] H) where
  toFun g := π g
  map_one' := by
    simp
  map_mul' g h := by
    simp

noncomputable def representationGroupRingHom
    (π : UnitaryRepresentation G H) :
    RationalGroupRing G →+* (H →L[ℂ] H) :=
  MonoidAlgebra.liftNCRingHom
    ((algebraMap ℂ (H →L[ℂ] H)).comp (algebraMap ℚ ℂ))
    (representationOperatorMonoidHom π)
    (fun q g ↦ by
      change Commute ((algebraMap ℂ (H →L[ℂ] H)) (q : ℂ))
        (representationOperatorMonoidHom π g)
      exact Algebra.commutes _ _)

@[simp]
theorem representationGroupRingHom_single
    (π : UnitaryRepresentation G H) (g : G) (r : ℚ) :
    representationGroupRingHom π (MonoidAlgebra.single g r) =
      (r : ℂ) • (π g : H →L[ℂ] H) := by
  simp [representationGroupRingHom, representationOperatorMonoidHom, Algebra.smul_def]

noncomputable def RationalGroupRing.adjoint
    (a : RationalGroupRing G) : RationalGroupRing G :=
  a.coeff.sum fun g r ↦ MonoidAlgebra.single g⁻¹ r

@[simp]
theorem RationalGroupRing.adjoint_single (g : G) (r : ℚ) :
    RationalGroupRing.adjoint (MonoidAlgebra.single g r) =
      MonoidAlgebra.single g⁻¹ r := by
  simp [RationalGroupRing.adjoint]

@[simp]
theorem RationalGroupRing.adjoint_apply
    (a : RationalGroupRing G) (g : G) :
    (RationalGroupRing.adjoint a).coeff g = a.coeff g⁻¹ := by
  classical
  refine MonoidAlgebra.induction a ?_ ?_
  · simp [RationalGroupRing.adjoint]
  · intro x r b _hx hr ih
    rw [show RationalGroupRing.adjoint (MonoidAlgebra.single x r + b) =
      RationalGroupRing.adjoint (MonoidAlgebra.single x r) +
        RationalGroupRing.adjoint b by
          simp [RationalGroupRing.adjoint, Finsupp.sum_add_index, hr]]
    simp [ih, Finsupp.single_apply, inv_eq_iff_eq_inv]

@[simp]
theorem RationalGroupRing.adjoint_zero :
    RationalGroupRing.adjoint (0 : RationalGroupRing G) = 0 := by
  simp [RationalGroupRing.adjoint]

@[simp]
theorem RationalGroupRing.adjoint_add
    (a b : RationalGroupRing G) :
    RationalGroupRing.adjoint (a + b) =
      RationalGroupRing.adjoint a + RationalGroupRing.adjoint b := by
  classical
  simp [RationalGroupRing.adjoint, Finsupp.sum_add_index]

@[simp]
theorem RationalGroupRing.adjoint_neg
    (a : RationalGroupRing G) :
    RationalGroupRing.adjoint (-a) =
      -RationalGroupRing.adjoint a := by
  ext g
  simp

@[simp]
theorem RationalGroupRing.adjoint_sub
    (a b : RationalGroupRing G) :
    RationalGroupRing.adjoint (a - b) =
      RationalGroupRing.adjoint a - RationalGroupRing.adjoint b := by
  simp [sub_eq_add_neg]

@[simp]
theorem RationalGroupRing.adjoint_smul
    (r : ℚ) (a : RationalGroupRing G) :
    RationalGroupRing.adjoint (r • a) =
      r • RationalGroupRing.adjoint a := by
  ext g
  simp

private theorem representationGroupRingHom_adjoint_single
    (π : UnitaryRepresentation G H) (g : G) (r : ℚ) :
    representationGroupRingHom π
        (RationalGroupRing.adjoint (MonoidAlgebra.single g r)) =
      star (representationGroupRingHom π (MonoidAlgebra.single g r)) := by
  rw [RationalGroupRing.adjoint_single]
  simp only [representationGroupRingHom, MonoidAlgebra.liftNCRingHom_single,
    RingHom.coe_comp, Function.comp_apply, representationOperatorMonoidHom,
    MonoidHom.coe_mk, OneHom.coe_mk, map_inv, star_mul]
  have hunit : (↑((π g)⁻¹) : H →L[ℂ] H) =
      star (↑(π g) : H →L[ℂ] H) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star]
  have hscalar :
      star ((algebraMap ℂ (H →L[ℂ] H)) ((algebraMap ℚ ℂ) r)) =
        (algebraMap ℂ (H →L[ℂ] H)) ((algebraMap ℚ ℂ) r) := by
    rw [← algebraMap_star_comm]
    simp
  rw [hunit, hscalar]
  exact
    (Algebra.commutes (R := ℂ) (A := H →L[ℂ] H)
      ((algebraMap ℚ ℂ) r) (star (↑(π g) : H →L[ℂ] H)))

theorem representationGroupRingHom_adjoint
    (π : UnitaryRepresentation G H) (a : RationalGroupRing G) :
    representationGroupRingHom π (RationalGroupRing.adjoint a) =
      star (representationGroupRingHom π a) := by
  classical
  refine MonoidAlgebra.induction a ?_ ?_
  · simp [RationalGroupRing.adjoint]
  · intro g r a _hg hr ih
    rw [show RationalGroupRing.adjoint (MonoidAlgebra.single g r + a) =
      RationalGroupRing.adjoint (MonoidAlgebra.single g r) +
        RationalGroupRing.adjoint a by
          simp [RationalGroupRing.adjoint, Finsupp.sum_add_index, hr]]
    rw [map_add, map_add, star_add,
      representationGroupRingHom_adjoint_single, ih]

noncomputable def RationalGroupRing.difference (g : G) : RationalGroupRing G :=
  MonoidAlgebra.single 1 1 - MonoidAlgebra.single g 1

noncomputable def RationalGroupRing.laplacian (K : Finset G) : RationalGroupRing G :=
  ∑ g ∈ K, RationalGroupRing.adjoint (RationalGroupRing.difference g) *
    RationalGroupRing.difference g

def RationalGroupRing.IsSumOfSquares (a : RationalGroupRing G) : Prop :=
  ∃ xs : List (RationalGroupRing G),
    a = (xs.map fun x ↦ RationalGroupRing.adjoint x * x).sum

def RationalGroupRing.IsPositiveSumOfSquares (a : RationalGroupRing G) : Prop :=
  ∃ xs : List (ℚ × RationalGroupRing G),
    (∀ x ∈ xs, 0 ≤ x.1) ∧
      a = (xs.map fun x ↦ x.1 •
        (RationalGroupRing.adjoint x.2 * x.2)).sum

@[simp]
theorem representationGroupRingHom_difference
    (π : UnitaryRepresentation G H) (g : G) :
    representationGroupRingHom π (RationalGroupRing.difference g) =
      1 - (π g : H →L[ℂ] H) := by
  simp [RationalGroupRing.difference]

@[simp]
theorem representationGroupRingHom_laplacian
    (π : UnitaryRepresentation G H) (K : Finset G) :
    representationGroupRingHom π (RationalGroupRing.laplacian K) =
      ∑ g ∈ K, star (1 - (π g : H →L[ℂ] H)) *
        (1 - (π g : H →L[ℂ] H)) := by
  classical
  simp [RationalGroupRing.laplacian, representationGroupRingHom_adjoint]

theorem RationalGroupRing.IsSumOfSquares.evaluation_nonneg
    {a : RationalGroupRing G} (ha : RationalGroupRing.IsSumOfSquares a)
    (π : UnitaryRepresentation G H) :
    0 ≤ representationGroupRingHom π a := by
  classical
  obtain ⟨xs, rfl⟩ := ha
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, map_add, map_mul,
        representationGroupRingHom_adjoint]
      exact add_nonneg (star_mul_self_nonneg _) ih

theorem RationalGroupRing.IsSumOfSquares.isPositiveSumOfSquares
    {a : RationalGroupRing G} (ha : RationalGroupRing.IsSumOfSquares a) :
    RationalGroupRing.IsPositiveSumOfSquares a := by
  obtain ⟨xs, rfl⟩ := ha
  refine ⟨xs.map fun x ↦ (1, x), ?_, ?_⟩
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    simp
  · rw [List.map_map]
    change (xs.map fun x ↦ RationalGroupRing.adjoint x * x).sum =
      (xs.map fun x ↦ (1 : ℚ) •
        (RationalGroupRing.adjoint x * x)).sum
    simp

theorem representationGroupRingHom_laplacian_nonneg
    (π : UnitaryRepresentation G H) (K : Finset G) :
    0 ≤ representationGroupRingHom π (RationalGroupRing.laplacian K) := by
  rw [representationGroupRingHom_laplacian]
  exact Finset.sum_nonneg fun g _ ↦ star_mul_self_nonneg _

theorem representationGroupRingHom_laplacian_energy
    (π : UnitaryRepresentation G H) (K : Finset G) (ξ : H) :
    RCLike.re ⟪representationGroupRingHom π
        (RationalGroupRing.laplacian K) ξ, ξ⟫_ℂ =
      ∑ g ∈ K, ‖((1 - (π g : H →L[ℂ] H)) ξ)‖ ^ 2 := by
  rw [representationGroupRingHom_laplacian, sum_apply, sum_inner, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [mul_apply_eq_comp]
  rw [show star (1 - (π g : H →L[ℂ] H)) =
    ContinuousLinearMap.adjoint (1 - (π g : H →L[ℂ] H)) by rfl]
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (norm_sq_eq_re_inner _).symm

theorem representationGroupRingHom_laplacian_apply_eq_zero_iff
    (π : UnitaryRepresentation G H) (K : Finset G) (ξ : H) :
    representationGroupRingHom π (RationalGroupRing.laplacian K) ξ = 0 ↔
      ∀ g ∈ K, (π g : H →L[ℂ] H) ξ = ξ := by
  constructor
  · intro hzero
    have hsum :
        ∑ g ∈ K, ‖((1 - (π g : H →L[ℂ] H)) ξ)‖ ^ 2 = 0 := by
      rw [← representationGroupRingHom_laplacian_energy π K ξ, hzero]
      simp
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun g _ ↦ sq_nonneg ‖((1 - (π g : H →L[ℂ] H)) ξ)‖)).mp hsum
    intro g hg
    have hnorm : ‖((1 - (π g : H →L[ℂ] H)) ξ)‖ = 0 :=
      (sq_eq_zero_iff).mp (hall g hg)
    have hdiff : (1 - (π g : H →L[ℂ] H)) ξ = 0 :=
      norm_eq_zero.mp hnorm
    exact (sub_eq_zero.mp (by simpa using hdiff)).symm
  · intro hfixed
    rw [representationGroupRingHom_laplacian, sum_apply]
    apply Finset.sum_eq_zero
    intro g hg
    rw [mul_apply_eq_comp]
    simp [hfixed g hg]

theorem representationGroupRingHom_smul
    (π : UnitaryRepresentation G H) (a : RationalGroupRing G) (r : ℚ) :
    representationGroupRingHom π (r • a) =
      (r : ℂ) • representationGroupRingHom π a := by
  rw [Algebra.smul_def, map_mul]
  change representationGroupRingHom π (MonoidAlgebra.single 1 r) * _ = _
  simp [Algebra.smul_def]

omit [CompleteSpace H] in

theorem rational_complex_smul_eq_real_smul
    (r : ℚ) (A : H →L[ℂ] H) :
    (r : ℂ) • A = (r : ℝ) • A := by
  ext x
  change (r : ℂ) • A x = ((r : ℝ) : ℂ) • A x
  norm_num

theorem RationalGroupRing.IsPositiveSumOfSquares.evaluation_nonneg
    {a : RationalGroupRing G}
    (ha : RationalGroupRing.IsPositiveSumOfSquares a)
    (π : UnitaryRepresentation G H) :
    0 ≤ representationGroupRingHom π a := by
  classical
  obtain ⟨xs, hweights, rfl⟩ := ha
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 ≤ x.1 := hweights x (by simp)
      have hxs : ∀ y ∈ xs, 0 ≤ y.1 := by
        intro y hy
        exact hweights y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, map_add,
        representationGroupRingHom_smul, map_mul,
        representationGroupRingHom_adjoint]
      rw [rational_complex_smul_eq_real_smul]
      exact add_nonneg (smul_nonneg (by exact_mod_cast hx) (star_mul_self_nonneg _))
        (ih hxs)

def RationalGroupRing.HasSpectralGapCertificate
    (K : Finset G) (r : ℚ) : Prop :=
  0 < r ∧ RationalGroupRing.IsPositiveSumOfSquares
    (RationalGroupRing.laplacian K * RationalGroupRing.laplacian K -
      r • RationalGroupRing.laplacian K)

theorem RationalGroupRing.HasSpectralGapCertificate.evaluation_nonneg
    {K : Finset G} {r : ℚ}
    (hcert : RationalGroupRing.HasSpectralGapCertificate K r)
    (π : UnitaryRepresentation G H) :
    0 ≤
      representationGroupRingHom π (RationalGroupRing.laplacian K) *
        representationGroupRingHom π (RationalGroupRing.laplacian K) -
          (r : ℝ) •
            representationGroupRingHom π (RationalGroupRing.laplacian K) := by
  have hn := hcert.2.evaluation_nonneg π
  rw [map_sub, map_mul, representationGroupRingHom_smul] at hn
  rwa [rational_complex_smul_eq_real_smul] at hn

theorem representationGroupRingHom_laplacian_apply_norm_le
    [Nontrivial H]
    (π : UnitaryRepresentation G H) (K : Finset G) (ξ : H) (ε : ℝ)
    (hclose : ∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ ≤ ε) :
    ‖representationGroupRingHom π (RationalGroupRing.laplacian K) ξ‖ ≤
      2 * K.card * ε := by
  rw [representationGroupRingHom_laplacian, sum_apply]
  calc
    ‖∑ g ∈ K, (star (1 - (π g : H →L[ℂ] H)) *
        (1 - (π g : H →L[ℂ] H))) ξ‖ ≤
        ∑ g ∈ K, ‖(star (1 - (π g : H →L[ℂ] H)) *
          (1 - (π g : H →L[ℂ] H))) ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _g ∈ K, 2 * ε := by
      apply Finset.sum_le_sum
      intro g hg
      rw [mul_apply_eq_comp]
      calc
        ‖star (1 - (π g : H →L[ℂ] H))
            ((1 - (π g : H →L[ℂ] H)) ξ)‖ ≤
            ‖star (1 - (π g : H →L[ℂ] H))‖ *
              ‖(1 - (π g : H →L[ℂ] H)) ξ‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ = ‖1 - (π g : H →L[ℂ] H)‖ *
              ‖(1 - (π g : H →L[ℂ] H)) ξ‖ := by rw [norm_star]
        _ ≤ 2 * ε := by
          apply mul_le_mul
          · calc
              ‖1 - (π g : H →L[ℂ] H)‖ ≤
                  ‖(1 : H →L[ℂ] H)‖ + ‖(π g : H →L[ℂ] H)‖ :=
                norm_sub_le _ _
              _ = 2 := by
                rw [norm_one, CStarRing.norm_coe_unitary]
                norm_num
          · simpa [norm_sub_rev] using hclose g hg
          · positivity
          · positivity
    _ = 2 * K.card * ε := by
      simp
      ring

theorem isUnit_of_nonneg_and_spectralGapPolynomial
    (A : H →L[ℂ] H) (r : ℝ) (hr : 0 < r)
    (hA : 0 ≤ A) (hpoly : 0 ≤ A * A - r • A)
    (hinj : Function.Injective A) :
    IsUnit A := by
  have hAsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hmul :
      cfc (fun x : ℝ ↦ x * x) A = A * A := by
    calc
      cfc (fun x : ℝ ↦ x * x) A =
          cfc (id : ℝ → ℝ) A * cfc (id : ℝ → ℝ) A :=
        cfc_mul (id : ℝ → ℝ) (id : ℝ → ℝ) A (by fun_prop) (by fun_prop)
      _ = A * A := by rw [cfc_id ℝ A hAsa]
  have hsmul :
      cfc (fun x : ℝ ↦ r * x) A = r • A := by
    calc
      cfc (fun x : ℝ ↦ r * x) A =
          cfc (fun x : ℝ ↦ r • id x) A := rfl
      _ = r • cfc (id : ℝ → ℝ) A :=
        cfc_smul r (id : ℝ → ℝ) A (by fun_prop)
      _ = r • A := by rw [cfc_id ℝ A hAsa]
  have hpoly_cfc :
      cfc (fun x : ℝ ↦ x * x - r * x) A = A * A - r • A := by
    calc
      cfc (fun x : ℝ ↦ x * x - r * x) A =
          cfc (fun x : ℝ ↦ x * x) A -
            cfc (fun x : ℝ ↦ r * x) A :=
        cfc_sub (fun x : ℝ ↦ x * x) (fun x : ℝ ↦ r * x) A
          (by fun_prop) (by fun_prop)
      _ = A * A - r • A := by rw [hmul, hsmul]
  have hspecA : ∀ x ∈ spectrum ℝ A, 0 ≤ x :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg A hAsa).mp hA
  have hspecPoly :
      ∀ y ∈ spectrum ℝ (A * A - r • A), 0 ≤ y :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg
      (A * A - r • A) (IsSelfAdjoint.of_nonneg hpoly)).mp hpoly
  have hgap : ∀ x ∈ spectrum ℝ A, x = 0 ∨ r ≤ x := by
    intro x hx
    have hmem : x * x - r * x ∈ spectrum ℝ (A * A - r • A) := by
      rw [← hpoly_cfc,
        cfc_map_spectrum (fun x : ℝ ↦ x * x - r * x) A hAsa (by fun_prop)]
      exact ⟨x, hx, rfl⟩
    have hxnonneg := hspecA x hx
    have hxpoly := hspecPoly _ hmem
    rcases eq_or_lt_of_le hxnonneg with rfl | hxpos
    · exact Or.inl rfl
    · exact Or.inr (by nlinarith)
  let f : ℝ → ℝ := fun x ↦ max 0 (1 - x / r)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hAf : A * cfc f A = 0 := by
    calc
      A * cfc f A = cfc (id : ℝ → ℝ) A * cfc f A := by
        rw [cfc_id ℝ A hAsa]
      _ = cfc (fun x : ℝ ↦ id x * f x) A :=
        (cfc_mul (id : ℝ → ℝ) f A (by fun_prop) hf.continuousOn).symm
      _ = cfc (0 : ℝ → ℝ) A := cfc_congr fun x hx ↦ by
        rcases hgap x hx with rfl | hxr
        · simp
        · have hle : 1 - x / r ≤ 0 := by
            rw [sub_nonpos]
            exact (one_le_div₀ hr).mpr hxr
          simp [f, max_eq_left hle]
      _ = 0 := cfc_zero ℝ A
  by_contra hnot
  have hzero : (0 : ℝ) ∈ spectrum ℝ A := by
    by_contra hz
    exact hnot ((spectrum.zero_notMem_iff ℝ).mp hz)
  have hone : (1 : ℝ) ∈ spectrum ℝ (cfc f A) := by
    rw [cfc_map_spectrum f A hAsa hf.continuousOn]
    exact ⟨0, hzero, by simp [f]⟩
  have hcfczero : cfc f A = 0 := by
    ext x
    apply hinj
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using
      DFunLike.congr_fun hAf x
  rw [hcfczero] at hone
  rw [spectrum.mem_iff] at hone
  exact hone (by simp)

theorem hasKazhdanPropertyT_of_spectralGapCertificate
    (G : CountableDiscreteGroup.{u}) (K : Finset G) (r : ℚ)
    (hgen : IsGeneratingSet G K)
    (hcert : RationalGroupRing.HasSpectralGapCertificate K r) :
    HasKazhdanPropertyT G := by
  intro H _ _ _ π hπ
  let A : H →L[ℂ] H :=
    representationGroupRingHom π (RationalGroupRing.laplacian K)
  by_contra hno
  have hinvariant_zero (x : H) (hx : π.IsInvariant x) : x = 0 := by
    by_contra hx0
    exact hno ⟨x, hx0, hx⟩
  have hAinj : Function.Injective A := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hinvariant_zero (x - y)
    have hAzero : A (x - y) = 0 := by
      simp only [A, map_sub, hxy, sub_self]
    exact π.isInvariant_of_isGeneratingSet K hgen (x - y)
      ((representationGroupRingHom_laplacian_apply_eq_zero_iff
        π K (x - y)).mp hAzero)
  have hAunit : IsUnit A :=
    isUnit_of_nonneg_and_spectralGapPolynomial A (r : ℝ)
      (by exact_mod_cast hcert.1)
      (representationGroupRingHom_laplacian_nonneg π K)
      (hcert.evaluation_nonneg π) hAinj
  let u : (H →L[ℂ] H)ˣ := hAunit.unit
  let B : H →L[ℂ] H := ↑u⁻¹
  have hu : (u : H →L[ℂ] H) = A := hAunit.unit_spec
  have hBA : B * A = 1 := by
    change (↑u⁻¹ : H →L[ℂ] H) * A = 1
    rw [← hu]
    exact Units.inv_mul u
  let ε : ℝ :=
    1 / (2 * ((K.card : ℝ) + 1) * (‖B‖ + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨ξ, hξnorm, hclose⟩ := hπ K ε hε
  have hξne : ξ ≠ 0 := by
    intro hξ
    rw [hξ, norm_zero] at hξnorm
    norm_num at hξnorm
  letI : Nontrivial H := ⟨⟨ξ, 0, hξne⟩⟩
  have hAnorm :
      ‖A ξ‖ ≤ 2 * K.card * ε := by
    exact representationGroupRingHom_laplacian_apply_norm_le
      π K ξ ε fun g hg ↦ (hclose g hg).le
  have hrecover : B (A ξ) = ξ := by
    have happ := DFunLike.congr_fun hBA ξ
    simpa [mul_apply_eq_comp] using happ
  have hnum :
      ‖B‖ * (2 * (K.card : ℝ)) <
        2 * ((K.card : ℝ) + 1) * (‖B‖ + 1) := by
    have hB : 0 ≤ ‖B‖ := norm_nonneg _
    have hK : 0 ≤ (K.card : ℝ) := by positivity
    nlinarith [mul_nonneg hB hK]
  have hden :
      0 < 2 * ((K.card : ℝ) + 1) * (‖B‖ + 1) := by positivity
  have hsmall : ‖B‖ * (2 * K.card * ε) < 1 := by
    dsimp [ε]
    rw [show ‖B‖ * (2 * (K.card : ℝ) *
        (1 / (2 * ((K.card : ℝ) + 1) * (‖B‖ + 1)))) =
      (‖B‖ * (2 * (K.card : ℝ))) /
        (2 * ((K.card : ℝ) + 1) * (‖B‖ + 1)) by ring]
    exact (div_lt_one hden).mpr hnum
  have hone_le : (1 : ℝ) ≤ ‖B‖ * (2 * K.card * ε) := by
    calc
      1 = ‖ξ‖ := hξnorm.symm
      _ = ‖B (A ξ)‖ := by rw [hrecover]
      _ ≤ ‖B‖ * ‖A ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B‖ * (2 * K.card * ε) :=
        mul_le_mul_of_nonneg_left hAnorm (norm_nonneg _)
  exact (not_lt_of_ge hone_le) hsmall

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateOrbitGroupRing

namespace ConnesRigidity

universe u v

namespace RationalGroupRing

variable {G : Type u} [Group G]

noncomputable local instance : DecidableEq G := Classical.decEq G

theorem IsPositiveSumOfSquares.zero :
    IsPositiveSumOfSquares (0 : RationalGroupRing G) := by
  refine ⟨[], ?_, ?_⟩
  · simp
  · simp

theorem IsPositiveSumOfSquares.add
    {a b : RationalGroupRing G}
    (ha : IsPositiveSumOfSquares a)
    (hb : IsPositiveSumOfSquares b) :
    IsPositiveSumOfSquares (a + b) := by
  obtain ⟨xs, hxs, rfl⟩ := ha
  obtain ⟨ys, hys, rfl⟩ := hb
  refine ⟨xs ++ ys, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxs x hx
    · exact hys x hx
  · simp [List.map_append, List.sum_append]

theorem IsPositiveSumOfSquares.sum
    {ι : Type v} (s : Finset ι)
    (f : ι → RationalGroupRing G)
    (hf : ∀ i ∈ s, IsPositiveSumOfSquares (f i)) :
    IsPositiveSumOfSquares (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPositiveSumOfSquares.zero (G := G)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem IsPositiveSumOfSquares.smul
    {a : RationalGroupRing G} (r : ℚ) (hr : 0 ≤ r)
    (ha : IsPositiveSumOfSquares a) :
    IsPositiveSumOfSquares (r • a) := by
  obtain ⟨xs, hxs, rfl⟩ := ha
  refine ⟨xs.map (fun x => (r * x.1, x.2)), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg hr (hxs y hy)
  · rw [List.smul_sum]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _hx
    change r • (x.1 • (adjoint x.2 * x.2)) =
      (r * x.1) • (adjoint x.2 * x.2)
    rw [smul_smul]

theorem IsPositiveSumOfSquares.map
    (f : RationalGroupRing G →+* RationalGroupRing G)
    (hf_smul : ∀ (r : ℚ) (x : RationalGroupRing G),
      f (r • x) = r • f x)
    (hf_adjoint : ∀ x : RationalGroupRing G,
      f (adjoint x) = adjoint (f x))
    {a : RationalGroupRing G}
    (ha : IsPositiveSumOfSquares a) :
    IsPositiveSumOfSquares (f a) := by
  obtain ⟨xs, hxs, rfl⟩ := ha
  refine ⟨xs.map (fun x => (x.1, f x.2)), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hxs y hy
  · rw [map_list_sum]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _hx
    change f (x.1 • (adjoint x.2 * x.2)) =
      x.1 • (adjoint (f x.2) * f x.2)
    rw [hf_smul, map_mul, hf_adjoint]

theorem IsPositiveSumOfSquares.map_groupRingMap
    (e : G ≃* G) {a : RationalGroupRing G}
    (ha : IsPositiveSumOfSquares a) :
    IsPositiveSumOfSquares
      (AffineSymplecticOrbitCertificate.groupRingMap e a) :=
  ha.map (AffineSymplecticOrbitCertificate.groupRingMap e)
    (AffineSymplecticOrbitCertificate.groupRingMap_smul e)
    (AffineSymplecticOrbitCertificate.groupRingMap_adjoint e)

theorem HasSpectralGapCertificate.map_groupRingMap
    (e : G ≃* G) {K : Finset G} {r : ℚ}
    (hcertificate : HasSpectralGapCertificate K r) :
    HasSpectralGapCertificate (K.image e) r := by
  refine ⟨hcertificate.1, ?_⟩
  have hpositive := hcertificate.2.map_groupRingMap e
  simpa only [map_sub, map_mul,
    AffineSymplecticOrbitCertificate.groupRingMap_smul,
    AffineSymplecticOrbitCertificate.groupRingMap_laplacian_image]
    using hpositive

theorem IsPositiveSumOfSquares.average
    {ι : Type v} (s : Finset ι)
    (f : ι → RationalGroupRing G)
    (hf : ∀ i ∈ s, IsPositiveSumOfSquares (f i)) :
    IsPositiveSumOfSquares
      (((s.card : ℚ)⁻¹) • ∑ i ∈ s, f i) := by
  apply (IsPositiveSumOfSquares.sum s f hf).smul
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

end RationalGroupRing

namespace AffineSymplecticOrbitCertificate

variable {G : Type u} [Group G]

noncomputable local instance : DecidableEq G := Classical.decEq G

noncomputable def groupRingSymmetryAverage {ι : Type v}
    (s : Finset ι) (symmetry : ι → G ≃* G)
    (a : RationalGroupRing G) : RationalGroupRing G :=
  ((s.card : ℚ)⁻¹) • ∑ i ∈ s, groupRingMap (symmetry i) a

theorem groupRingSymmetryAverage_isPositiveSumOfSquares
    {ι : Type v} (s : Finset ι) (symmetry : ι → G ≃* G)
    {a : RationalGroupRing G}
    (ha : RationalGroupRing.IsPositiveSumOfSquares a) :
    RationalGroupRing.IsPositiveSumOfSquares
      (groupRingSymmetryAverage s symmetry a) := by
  unfold groupRingSymmetryAverage
  apply RationalGroupRing.IsPositiveSumOfSquares.average
  intro i _hi
  exact ha.map_groupRingMap (symmetry i)

theorem groupRingSymmetryAverage_eq_of_fixed
    {ι : Type v} (s : Finset ι) (symmetry : ι → G ≃* G)
    (a : RationalGroupRing G) (hs : s.Nonempty)
    (hfixed : ∀ i ∈ s, groupRingMap (symmetry i) a = a) :
    groupRingSymmetryAverage s symmetry a = a := by
  classical
  unfold groupRingSymmetryAverage
  have hsum :
      (∑ i ∈ s, groupRingMap (symmetry i) a) = s.card • a := by
    calc
      (∑ i ∈ s, groupRingMap (symmetry i) a) = ∑ _i ∈ s, a :=
        Finset.sum_congr rfl hfixed
      _ = s.card • a := Finset.sum_const a
  rw [hsum, ← Nat.cast_smul_eq_nsmul ℚ, ← mul_smul]
  have hcard : (s.card : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  simp [hcard]

theorem groupRingMap_spectralGapPolynomial
    (e : G ≃* G) (K : Finset G) (r : ℚ) :
    groupRingMap e
        (RationalGroupRing.laplacian K * RationalGroupRing.laplacian K -
          r • RationalGroupRing.laplacian K) =
      RationalGroupRing.laplacian (K.image e) *
          RationalGroupRing.laplacian (K.image e) -
        r • RationalGroupRing.laplacian (K.image e) := by
  simp [groupRingMap_laplacian_image]

theorem groupRingMap_spectralGapPolynomial_of_image_eq
    (e : G ≃* G) (K : Finset G) (r : ℚ)
    (hK : K.image e = K) :
    groupRingMap e
        (RationalGroupRing.laplacian K * RationalGroupRing.laplacian K -
          r • RationalGroupRing.laplacian K) =
      RationalGroupRing.laplacian K * RationalGroupRing.laplacian K -
        r • RationalGroupRing.laplacian K := by
  rw [groupRingMap_spectralGapPolynomial, hK]

theorem groupRingSymmetryAverage_spectralGapPolynomial
    {ι : Type v} (s : Finset ι) (symmetry : ι → G ≃* G)
    (K : Finset G) (r : ℚ) (hs : s.Nonempty)
    (hK : ∀ i ∈ s, K.image (symmetry i) = K) :
    groupRingSymmetryAverage s symmetry
        (RationalGroupRing.laplacian K * RationalGroupRing.laplacian K -
          r • RationalGroupRing.laplacian K) =
      RationalGroupRing.laplacian K * RationalGroupRing.laplacian K -
        r • RationalGroupRing.laplacian K := by
  apply groupRingSymmetryAverage_eq_of_fixed _ _ _ hs
  intro i hi
  exact groupRingMap_spectralGapPolynomial_of_image_eq
    (symmetry i) K r (hK i hi)

end AffineSymplecticOrbitCertificate

end ConnesRigidity

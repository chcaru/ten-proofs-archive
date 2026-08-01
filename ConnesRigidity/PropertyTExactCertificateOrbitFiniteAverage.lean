
import ConnesRigidity.PropertyTExactCertificateOrbitAverage

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

universe u v

variable {G : Type u} [Group G]

noncomputable local instance : DecidableEq G := Classical.decEq G

@[simp]
theorem groupRingMap_coeff
    (e : G ≃* G) (a : RationalGroupRing G) (g : G) :
    (groupRingMap e a).coeff (e g) = a.coeff g := by
  change
    ((MonoidAlgebra.mapDomainRingEquiv ℚ e) a).coeff (e g) = a.coeff g
  rw [MonoidAlgebra.coeff_mapDomainRingEquiv,
    Finsupp.equivMapDomain_apply]
  simp

theorem groupRingMap_groupRingSymmetryAverage
    {ι : Type v} (s : Finset ι) (symmetry : ι → G ≃* G)
    (e : G ≃* G) (a : RationalGroupRing G) :
    groupRingMap e (groupRingSymmetryAverage s symmetry a) =
      groupRingSymmetryAverage s (fun i => (symmetry i).trans e) a := by
  classical
  unfold groupRingSymmetryAverage
  simp only [groupRingMap_smul, map_sum, groupRingMap_comp]

theorem groupRingSymmetryAverage_invariant_of_perm
    {ι : Type v} (s : Finset ι) (symmetry : ι → G ≃* G)
    (e : G ≃* G) (permutation : ι ≃ ι)
    (hpermutation : s.image permutation = s)
    (hcomposition : ∀ i ∈ s, (symmetry i).trans e = symmetry (permutation i))
    (a : RationalGroupRing G) :
    groupRingMap e (groupRingSymmetryAverage s symmetry a) =
      groupRingSymmetryAverage s symmetry a := by
  classical
  rw [groupRingMap_groupRingSymmetryAverage]
  unfold groupRingSymmetryAverage
  congr 1
  calc
    (∑ i ∈ s, groupRingMap ((symmetry i).trans e) a) =
        ∑ i ∈ s, groupRingMap (symmetry (permutation i)) a := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcomposition i hi]
    _ = ∑ i ∈ s.image permutation, groupRingMap (symmetry i) a := by
          rw [Finset.sum_image]
          intro i _hi j _hj heq
          exact permutation.injective heq
    _ = ∑ i ∈ s, groupRingMap (symmetry i) a := by
          rw [hpermutation]

theorem groupRingSymmetryAverage_coeff_invariant_of_perm
    {ι : Type v} (s : Finset ι) (symmetry : ι → G ≃* G)
    (e : G ≃* G) (permutation : ι ≃ ι)
    (hpermutation : s.image permutation = s)
    (hcomposition : ∀ i ∈ s, (symmetry i).trans e = symmetry (permutation i))
    (a : RationalGroupRing G) (g : G) :
    (groupRingSymmetryAverage s symmetry a).coeff (e g) =
      (groupRingSymmetryAverage s symmetry a).coeff g := by
  calc
    (groupRingSymmetryAverage s symmetry a).coeff (e g) =
        (groupRingMap e (groupRingSymmetryAverage s symmetry a)).coeff
          (e g) := by
            rw [groupRingSymmetryAverage_invariant_of_perm
              s symmetry e permutation hpermutation hcomposition]
    _ = (groupRingSymmetryAverage s symmetry a).coeff g :=
      groupRingMap_coeff e (groupRingSymmetryAverage s symmetry a) g

theorem groupRingSymmetryAverage_univ_invariant_of_perm
    {ι : Type v} [Fintype ι]
    (symmetry : ι → G ≃* G) (e : G ≃* G)
    (permutation : ι ≃ ι)
    (hcomposition : ∀ i, (symmetry i).trans e = symmetry (permutation i))
    (a : RationalGroupRing G) :
    groupRingMap e
        (groupRingSymmetryAverage Finset.univ symmetry a) =
      groupRingSymmetryAverage Finset.univ symmetry a := by
  classical
  apply groupRingSymmetryAverage_invariant_of_perm
    Finset.univ symmetry e permutation
  · exact Finset.image_univ_equiv permutation
  · intro i _hi
    exact hcomposition i

theorem groupRingSymmetryAverage_univ_coeff_invariant_of_perm
    {ι : Type v} [Fintype ι]
    (symmetry : ι → G ≃* G) (e : G ≃* G)
    (permutation : ι ≃ ι)
    (hcomposition : ∀ i, (symmetry i).trans e = symmetry (permutation i))
    (a : RationalGroupRing G) (g : G) :
    (groupRingSymmetryAverage Finset.univ symmetry a).coeff (e g) =
      (groupRingSymmetryAverage Finset.univ symmetry a).coeff g := by
  classical
  exact groupRingSymmetryAverage_coeff_invariant_of_perm
    Finset.univ symmetry e permutation
    (Finset.image_univ_equiv permutation)
    (fun i _hi => hcomposition i) a g

end ConnesRigidity.AffineSymplecticOrbitCertificate

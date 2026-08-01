
import ConnesRigidity.PropertyTExactCertificateOrbitAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitBasis
import ConnesRigidity.PropertyTExactCertificateOrbitBasisPermutation
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientIncidenceConcrete
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientIncidenceFinal
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientOrbitDisjointnessProof
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTermRegroup
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportFastValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitCoverage
import ConnesRigidity.PropertyTExactCertificateOrbitData
import ConnesRigidity.PropertyTExactCertificateOrbitGeneratorEnumeration
import ConnesRigidity.PropertyTExactCertificateOrbitGeneratorTransport
import ConnesRigidity.PropertyTExactCertificateOrbitGroupRing
import ConnesRigidity.PropertyTExactCertificateOrbitPairCoefficientCoverage
import ConnesRigidity.PropertyTExactCertificateOrbitPairOrbitSaturation
import ConnesRigidity.PropertyTExactCertificateOrbitTargetSemanticSoundness
import ConnesRigidity.GammaZeroGenerators

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

universe u v

variable {G : Type u} [Group G]

noncomputable local instance :
    DecidableEq constructedGammaZeroGroup := Classical.decEq _

theorem rationalGroupRing_adjoint_mul
    (left right : RationalGroupRing G) :
    RationalGroupRing.adjoint (left * right) =
      RationalGroupRing.adjoint right * RationalGroupRing.adjoint left := by
  classical
  have hsingle (g : G) (r : ℚ) (right : RationalGroupRing G) :
      RationalGroupRing.adjoint (MonoidAlgebra.single g r * right) =
        RationalGroupRing.adjoint right *
          RationalGroupRing.adjoint (MonoidAlgebra.single g r) := by
    induction right using MonoidAlgebra.induction with
    | zero => simp
    | single_add h s right _hh _hs ih =>
        simp [mul_add, add_mul, RationalGroupRing.adjoint_add, ih,
          MonoidAlgebra.single_mul_single,
          RationalGroupRing.adjoint_single, mul_comm]
  induction left using MonoidAlgebra.induction with
  | zero => simp
  | single_add g r left _hg _hr ih =>
      simp [add_mul, RationalGroupRing.adjoint_add, ih,
        mul_add, hsingle]

theorem orbitElementaryGenerators_inverse_closed :
    gammaZeroElementaryGenerators.image Inv.inv =
      gammaZeroElementaryGenerators := by
  classical
  ext g
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simp only [gammaZeroElementaryGenerators, Finset.mem_union,
      Finset.mem_image] at hh ⊢
    rcases hh with hh | ⟨k, hk, rfl⟩
    · exact Or.inr ⟨h, hh, rfl⟩
    · simpa using Or.inl hk
  · intro hg
    refine ⟨g⁻¹, ?_, by simp⟩
    simp only [gammaZeroElementaryGenerators, Finset.mem_union,
      Finset.mem_image] at hg ⊢
    rcases hg with hg | ⟨h, hh, rfl⟩
    · exact Or.inr ⟨g, hg, rfl⟩
    · simpa using Or.inl hh

noncomputable def orbitSpectralTarget :
    RationalGroupRing constructedGammaZeroGroup :=
  (certificateDenominator : ℚ) •
    ((4 : ℚ) •
        (RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators *
          RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators) -
      (1 / 25 : ℚ) •
        RationalGroupRing.customaryLaplacian
          gammaZeroElementaryGenerators)

theorem orbitSpectralTarget_groupRingMap
    (e : constructedGammaZeroGroup ≃* constructedGammaZeroGroup)
    (hgenerators : gammaZeroElementaryGenerators.image e =
      gammaZeroElementaryGenerators) :
    groupRingMap e orbitSpectralTarget = orbitSpectralTarget := by
  unfold orbitSpectralTarget
  rw [groupRingMap_smul, map_sub, groupRingMap_smul, map_mul,
    groupRingMap_customaryLaplacian_of_image_eq e _ hgenerators,
    groupRingMap_smul,
    groupRingMap_customaryLaplacian_of_image_eq e _ hgenerators]

theorem orbitSpectralTarget_adjoint :
    RationalGroupRing.adjoint orbitSpectralTarget =
      orbitSpectralTarget := by
  unfold orbitSpectralTarget
  rw [RationalGroupRing.adjoint_smul,
    RationalGroupRing.adjoint_sub,
    RationalGroupRing.adjoint_smul,
    rationalGroupRing_adjoint_mul,
    RationalGroupRing.adjoint_customaryLaplacian
      gammaZeroElementaryGenerators
      orbitElementaryGenerators_inverse_closed,
    RationalGroupRing.adjoint_smul,
    RationalGroupRing.adjoint_customaryLaplacian
      gammaZeroElementaryGenerators
      orbitElementaryGenerators_inverse_closed]

theorem mem_customaryLaplacian_support
    (generators : Finset G) {g : G}
    (hg : g ∈
      (RationalGroupRing.customaryLaplacian generators).coeff.support) :
    g = 1 ∨ g ∈ generators := by
  classical
  by_contra hmissing
  push Not at hmissing
  apply Finsupp.mem_support_iff.mp hg
  simp [RationalGroupRing.customaryLaplacian,
    RationalGroupRing.difference, Finsupp.single_apply,
    hmissing.1, hmissing.2, eq_comm]

theorem mem_customaryPolynomial_support_basisPair
    {ι : Type v} [DecidableEq G]
    (basis : ι → G) (generators : Finset G)
    (hone : ∃ i, basis i = 1)
    (hgenerators : ∀ g ∈ generators, ∃ i, basis i = g)
    (hinverse : generators.image Inv.inv = generators)
    (quadratic linear scale : ℚ) {g : G}
    (hg : g ∈
      (scale •
        (quadratic •
            (RationalGroupRing.customaryLaplacian generators *
              RationalGroupRing.customaryLaplacian generators) -
          linear •
            RationalGroupRing.customaryLaplacian generators)).coeff.support) :
    ∃ i j, (basis i)⁻¹ * basis j = g := by
  classical
  let laplacian := RationalGroupRing.customaryLaplacian generators
  have hpair_of_support {x y : G}
      (hx : x ∈ laplacian.coeff.support)
      (hy : y ∈ laplacian.coeff.support) :
      ∃ i j, (basis i)⁻¹ * basis j = x * y := by
    have hx' := mem_customaryLaplacian_support generators hx
    have hy' := mem_customaryLaplacian_support generators hy
    obtain ⟨i, hi⟩ : ∃ i, basis i = x⁻¹ := by
      rcases hx' with rfl | hx'
      · simpa using hone
      · apply hgenerators x⁻¹
        rw [← hinverse]
        exact Finset.mem_image.mpr ⟨x, hx', rfl⟩
    obtain ⟨j, hj⟩ : ∃ j, basis j = y := by
      rcases hy' with rfl | hy'
      · exact hone
      · exact hgenerators y hy'
    exact ⟨i, j, by rw [hi, hj, inv_inv]⟩
  by_contra hmissing
  push Not at hmissing
  have hlinear : laplacian.coeff g = 0 := by
    by_contra hnonzero
    have hsupport := Finsupp.mem_support_iff.mpr hnonzero
    have hshape := mem_customaryLaplacian_support generators hsupport
    rcases hshape with rfl | hgenerator
    · obtain ⟨i, hi⟩ := hone
      exact hmissing i i (by simp)
    · obtain ⟨i, hi⟩ := hone
      obtain ⟨j, hj⟩ := hgenerators g hgenerator
      exact hmissing i j (by simp [hi, hj])
  have hquadratic : (laplacian * laplacian).coeff g = 0 := by
    by_contra hnonzero
    have hsupport := Finsupp.mem_support_iff.mpr hnonzero
    have hproduct :=
      MonoidAlgebra.support_coeff_mul_subset laplacian laplacian hsupport
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_mul.mp hproduct
    obtain ⟨i, j, hij⟩ := hpair_of_support hx hy
    exact hmissing i j (hij.trans hxy)
  have hnonzero := Finsupp.mem_support_iff.mp hg
  apply hnonzero
  change
    scale * (quadratic * (laplacian * laplacian).coeff g -
      linear * laplacian.coeff g) = 0
  rw [hlinear, hquadratic]
  ring

theorem groupRingMap_fullGramExpansion
    {ι : Type v} [Fintype ι]
    (e : G ≃* G) (basis : ι → G) (gram : ι → ι → ℚ) :
    groupRingMap e (fullGramExpansion basis gram) =
      fullGramExpansion (fun i => e (basis i)) gram := by
  classical
  unfold fullGramExpansion
  simp only [map_sum, groupRingMap_smul, groupRingMap_single,
    map_mul, map_inv]

theorem fullGramExpansion_reindex
    {ι : Type v} [Fintype ι]
    (basis : ι → G) (gram : ι → ι → ℚ)
    (permutation : ι ≃ ι)
    (hgram : ∀ i j, gram (permutation i) (permutation j) = gram i j) :
    fullGramExpansion (fun i => basis (permutation i)) gram =
      fullGramExpansion basis gram := by
  classical
  unfold fullGramExpansion
  calc
    (∑ i, ∑ j, gram i j •
        MonoidAlgebra.single
          ((basis (permutation i))⁻¹ * basis (permutation j)) (1 : ℚ)) =
      ∑ i, ∑ j, gram (permutation i) (permutation j) •
        MonoidAlgebra.single
          ((basis (permutation i))⁻¹ * basis (permutation j)) (1 : ℚ) := by
            simp_rw [hgram]
    _ = _ := by
      calc
        (∑ i, ∑ j, gram (permutation i) (permutation j) •
            MonoidAlgebra.single
              ((basis (permutation i))⁻¹ * basis (permutation j))
              (1 : ℚ)) =
          ∑ i, ∑ j, gram (permutation i) j •
            MonoidAlgebra.single
              ((basis (permutation i))⁻¹ * basis j) (1 : ℚ) := by
                apply Finset.sum_congr rfl
                intro i _
                exact Equiv.sum_comp permutation
                  (fun j : ι => gram (permutation i) j •
                    MonoidAlgebra.single
                      ((basis (permutation i))⁻¹ * basis j) (1 : ℚ))
        _ = _ := Equiv.sum_comp permutation
          (fun i : ι => ∑ j, gram i j •
            MonoidAlgebra.single ((basis i)⁻¹ * basis j) (1 : ℚ))

theorem fullGramExpansion_groupRingMap
    {ι : Type v} [Fintype ι]
    (e : G ≃* G) (basis : ι → G) (gram : ι → ι → ℚ)
    (permutation : ι ≃ ι)
    (hbasis : ∀ i, e (basis i) = basis (permutation i))
    (hgram : ∀ i j, gram (permutation i) (permutation j) = gram i j) :
    groupRingMap e (fullGramExpansion basis gram) =
      fullGramExpansion basis gram := by
  rw [groupRingMap_fullGramExpansion]
  simp_rw [hbasis]
  exact fullGramExpansion_reindex basis gram permutation hgram

theorem fullGramExpansion_adjoint
    {ι : Type v} [Fintype ι]
    (basis : ι → G) (gram : ι → ι → ℚ)
    (hgram : ∀ i j, gram i j = gram j i) :
    RationalGroupRing.adjoint (fullGramExpansion basis gram) =
      fullGramExpansion basis gram := by
  classical
  unfold fullGramExpansion
  simp_rw [RationalGroupRing.adjoint_sum,
    RationalGroupRing.adjoint_smul,
    RationalGroupRing.adjoint_single]
  simp only [mul_inv_rev, inv_inv]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hgram j i]

noncomputable def orbitGramExpansion :
    RationalGroupRing constructedGammaZeroGroup :=
  fullGramExpansion orbitBasis
    (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ))

theorem orbitGramExpansion_groupRingMap_of_invariant_entries
    (hgram : ∀ symmetry : OrbitSymmetry, ∀ i j : Fin 425,
      gramEntry (symmetry • i).val (symmetry • j).val =
        gramEntry i.val j.val)
    (symmetry : Fin 64) :
    groupRingMap (orbitSymmetry symmetry) orbitGramExpansion =
      orbitGramExpansion := by
  let signedSymmetry : OrbitSymmetry := ⟨symmetry⟩
  unfold orbitGramExpansion
  apply fullGramExpansion_groupRingMap
    (orbitSymmetry symmetry) orbitBasis
    (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ))
    (orbitBasisPermutationEquiv signedSymmetry)
  · intro i
    exact orbitSymmetry_basis_action signedSymmetry i
  · intro i j
    exact_mod_cast hgram signedSymmetry i j

theorem orbitGramExpansion_representative_of_checked_fibers
    (pairKey : Fin 425 → Fin 425 → Fin 2256)
    (hpairKey : ∀ left right,
      (pairKey left right).val = pairOrbit left.val right.val)
    (hfibers : ∀ (coefficient : Fin 995) (gram : Fin 2256),
      gramPairFiberCount orbitBasis pairKey gram
          (coefficientRepresentativeElement coefficient.val) =
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
        then (gramOrbitIncidence gram.val).toNat else 0)
    (coefficient : Fin 995) :
    orbitGramExpansion.coeff
        (coefficientRepresentativeElement coefficient.val) =
      (coefficientOrbitTarget coefficient.val : ℚ) := by
  unfold orbitGramExpansion
  exact orbitGramRepresentative_coeff_of_fibers_and_terms
    pairKey hpairKey coefficient (hfibers coefficient)
    (orbitGramIncidence_weighted_sum_eq_target coefficient)

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_witnesses
    (hgenerators : ∀ s : Fin 64,
      gammaZeroElementaryGenerators.image (orbitSymmetry s) =
        gammaZeroElementaryGenerators)
    (hbasis_zero : orbitBasis (0 : Fin 425) = 1)
    (hgenerator_basis : ∀ g ∈ gammaZeroElementaryGenerators,
      ∃ i : Fin 425, orbitBasis i = g)
    (hgram_symmetry : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hgram_invariant : ∀ s : Fin 64,
      groupRingMap (orbitSymmetry s) orbitGramExpansion =
        orbitGramExpansion)
    (hpair_witness : ∀ i j : Fin 425,
      ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
        (orbitBasis i)⁻¹ * orbitBasis j =
          orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
        (orbitBasis i)⁻¹ * orbitBasis j =
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement orbit.val))⁻¹)
    (hrepresentative : ∀ orbit : Fin 995,
      orbitGramExpansion.coeff
          (coefficientRepresentativeElement orbit.val) =
        orbitSpectralTarget.coeff
          (coefficientRepresentativeElement orbit.val)) :
    orbitGramExpansion = orbitSpectralTarget := by
  apply groupRing_eq_of_invariant_orbit_coefficients
    orbitGramExpansion orbitSpectralTarget
    (fun orbit : Fin 995 => coefficientRepresentativeElement orbit.val)
    orbitSymmetry
  · exact hgram_invariant
  · intro symmetry
    exact orbitSpectralTarget_groupRingMap
      (orbitSymmetry symmetry) (hgenerators symmetry)
  · unfold orbitGramExpansion
    apply fullGramExpansion_adjoint
    intro i j
    exact_mod_cast hgram_symmetry i j
  · exact orbitSpectralTarget_adjoint
  · intro g hg
    rcases Finset.mem_union.mp hg with hgram | htarget
    · obtain ⟨i, j, hpair⟩ :=
        mem_fullGramExpansion_support orbitBasis
          (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)) hgram
      obtain ⟨orbit, symmetry, hwitness⟩ := hpair_witness i j
      exact ⟨orbit, symmetry, hpair.symm ▸ hwitness⟩
    · change g ∈
        (((certificateDenominator : ℚ) •
          ((4 : ℚ) •
              (RationalGroupRing.customaryLaplacian
                  gammaZeroElementaryGenerators *
                RationalGroupRing.customaryLaplacian
                  gammaZeroElementaryGenerators) -
            (1 / 25 : ℚ) •
              RationalGroupRing.customaryLaplacian
                gammaZeroElementaryGenerators)).coeff.support) at htarget
      obtain ⟨i, j, hpair⟩ :=
        mem_customaryPolynomial_support_basisPair
          orbitBasis gammaZeroElementaryGenerators
          ⟨0, hbasis_zero⟩ hgenerator_basis
          orbitElementaryGenerators_inverse_closed
          4 (1 / 25) certificateDenominator htarget
      obtain ⟨orbit, symmetry, hwitness⟩ := hpair_witness i j
      exact ⟨orbit, symmetry, hpair.symm ▸ hwitness⟩
  · exact hrepresentative

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_checked_representatives
    (hgenerators : ∀ s : Fin 64,
      gammaZeroElementaryGenerators.image (orbitSymmetry s) =
        gammaZeroElementaryGenerators)
    (hbasis_zero : orbitBasis (0 : Fin 425) = 1)
    (hgenerator_basis : ∀ g ∈ gammaZeroElementaryGenerators,
      ∃ i : Fin 425, orbitBasis i = g)
    (hgram_symmetry : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hgram_invariant : ∀ s : Fin 64,
      groupRingMap (orbitSymmetry s) orbitGramExpansion =
        orbitGramExpansion)
    (hpair_witness : ∀ i j : Fin 425,
      ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
        (orbitBasis i)⁻¹ * orbitBasis j =
          orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
        (orbitBasis i)⁻¹ * orbitBasis j =
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement orbit.val))⁻¹)
    (hgram_representative : ∀ orbit : Fin 995,
      orbitGramExpansion.coeff
          (coefficientRepresentativeElement orbit.val) =
        (coefficientOrbitTarget orbit.val : ℚ))
    (htarget_representative : ∀ orbit : Fin 995,
      orbitSpectralTarget.coeff
          (coefficientRepresentativeElement orbit.val) =
        (coefficientOrbitTarget orbit.val : ℚ)) :
    orbitGramExpansion = orbitSpectralTarget := by
  apply orbitGramExpansion_eq_orbitSpectralTarget_of_witnesses
    hgenerators hbasis_zero hgenerator_basis hgram_symmetry
    hgram_invariant hpair_witness
  intro orbit
  exact (hgram_representative orbit).trans
    (htarget_representative orbit).symm

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_orbit_checks
    (hgram_symmetry : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hgram_invariant : ∀ s : Fin 64,
      groupRingMap (orbitSymmetry s) orbitGramExpansion =
        orbitGramExpansion)
    (hpair_witness : ∀ i j : Fin 425,
      ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
        (orbitBasis i)⁻¹ * orbitBasis j =
          orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
        (orbitBasis i)⁻¹ * orbitBasis j =
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement orbit.val))⁻¹)
    (hgram_representative : ∀ orbit : Fin 995,
      orbitGramExpansion.coeff
          (coefficientRepresentativeElement orbit.val) =
        (coefficientOrbitTarget orbit.val : ℚ))
    (htarget_representative : ∀ orbit : Fin 995,
      orbitSpectralTarget.coeff
          (coefficientRepresentativeElement orbit.val) =
        (coefficientOrbitTarget orbit.val : ℚ)) :
    orbitGramExpansion = orbitSpectralTarget := by
  apply orbitGramExpansion_eq_orbitSpectralTarget_of_checked_representatives
    (hbasis_zero := orbitBasis_zero)
    (hgenerator_basis := generator_mem_orbitBasis)
    (hgram_symmetry := hgram_symmetry)
    (hgram_invariant := hgram_invariant)
    (hpair_witness := hpair_witness)
    (hgram_representative := hgram_representative)
    (htarget_representative := htarget_representative)
  intro symmetry
  ext generator
  simpa only [Finset.mem_image] using
    Finset.ext_iff.mp (orbitSymmetry_generators_image symmetry) generator

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_semantic_witnesses
    (hgram_symmetry : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hgram_action : ∀ symmetry : OrbitSymmetry, ∀ i j : Fin 425,
      gramEntry (symmetry • i).val (symmetry • j).val =
        gramEntry i.val j.val)
    (hpair_witness : ∀ i j : Fin 425,
      ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
        (orbitBasis i)⁻¹ * orbitBasis j =
          orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
        (orbitBasis i)⁻¹ * orbitBasis j =
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement orbit.val))⁻¹)
    (hgram_representative : ∀ orbit : Fin 995,
      orbitGramExpansion.coeff
          (coefficientRepresentativeElement orbit.val) =
        (coefficientOrbitTarget orbit.val : ℚ))
    (htarget_representative : ∀ orbit : Fin 995,
      orbitSpectralTarget.coeff
          (coefficientRepresentativeElement orbit.val) =
        (coefficientOrbitTarget orbit.val : ℚ)) :
    orbitGramExpansion = orbitSpectralTarget := by
  apply orbitGramExpansion_eq_orbitSpectralTarget_of_orbit_checks
    hgram_symmetry
    (orbitGramExpansion_groupRingMap_of_invariant_entries hgram_action)
    hpair_witness hgram_representative htarget_representative

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_gram_witnesses
    (hgram_symmetry : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hgram_action : ∀ symmetry : OrbitSymmetry, ∀ i j : Fin 425,
      gramEntry (symmetry • i).val (symmetry • j).val =
        gramEntry i.val j.val)
    (hpair_witness : ∀ i j : Fin 425,
      ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
        (orbitBasis i)⁻¹ * orbitBasis j =
          orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
        (orbitBasis i)⁻¹ * orbitBasis j =
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement orbit.val))⁻¹)
    (hgram_representative : ∀ orbit : Fin 995,
      orbitGramExpansion.coeff
          (coefficientRepresentativeElement orbit.val) =
        (coefficientOrbitTarget orbit.val : ℚ)) :
    orbitGramExpansion = orbitSpectralTarget := by
  apply orbitGramExpansion_eq_orbitSpectralTarget_of_semantic_witnesses
    hgram_symmetry hgram_action hpair_witness hgram_representative
  intro orbit
  simpa [orbitSpectralTarget] using orbitTargetRepresentative_coeff orbit

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_fiber_witnesses
    (hgram_symmetry : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hgram_action : ∀ symmetry : OrbitSymmetry, ∀ i j : Fin 425,
      gramEntry (symmetry • i).val (symmetry • j).val =
        gramEntry i.val j.val)
    (hpair_witness : ∀ i j : Fin 425,
      ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
        (orbitBasis i)⁻¹ * orbitBasis j =
          orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
        (orbitBasis i)⁻¹ * orbitBasis j =
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement orbit.val))⁻¹)
    (pairKey : Fin 425 → Fin 425 → Fin 2256)
    (hpairKey : ∀ left right,
      (pairKey left right).val = pairOrbit left.val right.val)
    (hfibers : ∀ (coefficient : Fin 995) (gram : Fin 2256),
      gramPairFiberCount orbitBasis pairKey gram
          (coefficientRepresentativeElement coefficient.val) =
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
        then (gramOrbitIncidence gram.val).toNat else 0) :
    orbitGramExpansion = orbitSpectralTarget := by
  exact orbitGramExpansion_eq_orbitSpectralTarget_of_gram_witnesses
    hgram_symmetry hgram_action hpair_witness
    (orbitGramExpansion_representative_of_checked_fibers
      pairKey hpairKey hfibers)

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_coverage_and_fibers
    (hpair_witness : ∀ i j : Fin 425,
      ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
        (orbitBasis i)⁻¹ * orbitBasis j =
          orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
        (orbitBasis i)⁻¹ * orbitBasis j =
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement orbit.val))⁻¹)
    (hfibers : ∀ (coefficient : Fin 995) (gram : Fin 2256),
      gramPairFiberCount orbitBasis orbitPairKey gram
          (coefficientRepresentativeElement coefficient.val) =
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
        then (gramOrbitIncidence gram.val).toNat else 0) :
    orbitGramExpansion = orbitSpectralTarget := by
  exact orbitGramExpansion_eq_orbitSpectralTarget_of_fiber_witnesses
    (fun i j => (gramEntry_swap i j).symm)
    gramEntry_symmetry hpair_witness
    orbitPairKey (fun _ _ => rfl) hfibers

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_transport_and_disjoint
    (htransport : ∀ gram : Fin 2256,
      coefficientRepresentativeElement
          (gramOrbitCoefficientOrbit gram.val).toNat ∈
        MulAction.orbit OrbitSignedSymmetry
          ((orbitBasis (orbitGramRepresentative gram).1)⁻¹ *
            orbitBasis (orbitGramRepresentative gram).2))
    (hdisjoint : ∀ first second : Fin 995,
      coefficientRepresentativeElement first.val ∈
        MulAction.orbit OrbitSignedSymmetry
          (coefficientRepresentativeElement second.val) →
      first = second) :
    orbitGramExpansion = orbitSpectralTarget := by
  apply orbitGramExpansion_eq_orbitSpectralTarget_of_coverage_and_fibers
    (orbitGramPair_coefficientRepresentative_coverage_of_transport htransport)
  apply orbitGramPairFiberCount_eq_checked_of_transport_and_disjoint
    (hdisjoint := hdisjoint)
  intro gram
  simpa [orbitGramCoefficientKey] using htransport gram

theorem orbitGramExpansion_eq_orbitSpectralTarget_of_disjoint
    (hdisjoint : ∀ first second : Fin 995,
      coefficientRepresentativeElement first.val ∈
        MulAction.orbit OrbitSignedSymmetry
          (coefficientRepresentativeElement second.val) →
      first = second) :
    orbitGramExpansion = orbitSpectralTarget := by
  apply orbitGramExpansion_eq_orbitSpectralTarget_of_transport_and_disjoint
    (hdisjoint := hdisjoint)
  exact orbitGram_coefficientRepresentative_mem_of_transport
    orbitCoefficientTransportPacketsCheck_valid

theorem orbitGramExpansion_eq_orbitSpectralTarget :
    orbitGramExpansion = orbitSpectralTarget :=
  orbitGramExpansion_eq_orbitSpectralTarget_of_disjoint
    coefficientRepresentative_orbits_disjoint

end ConnesRigidity.AffineSymplecticOrbitCertificate

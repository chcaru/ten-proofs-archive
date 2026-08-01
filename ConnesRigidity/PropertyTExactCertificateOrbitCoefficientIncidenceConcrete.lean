


import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientIncidence
import ConnesRigidity.PropertyTExactCertificateOrbitBasisPermutation
import ConnesRigidity.PropertyTExactCertificateOrbitCheckerSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
import ConnesRigidity.PropertyTExactCertificateOrbitInvariantWitness
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidation
import ConnesRigidity.PropertyTExactCertificateOrbitTransportValidation













namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000


theorem orbitGramCoefficientOrbit_lt (gram : Fin 2256) :
    (gramOrbitCoefficientOrbit gram.val).toNat < 995 := by
  have hindex : gram.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  have hfields := orbitGramRepresentativeFields_valid gram.val hindex
  let row := gramOrbitData[gram.val]
  have hrow : gramOrbitData[gram.val]? = some row := by
    simp [row, hindex]
  have hfield :
      gramOrbitCoefficientOrbit gram.val = orbitEntry row 2 := by
    simp [gramOrbitCoefficientOrbit, dataEntry,
      Array.getD_eq_getD_getElem?, hrow, orbitEntry]
  rw [hfield]
  have hbounds : 0 ≤ orbitEntry row 2 ∧ orbitEntry row 2 < (995 : Int) := by
    simpa [row, coefficientRepresentativeData_size] using
      hfields.2.2.2.1
  exact (Int.toNat_lt hbounds.1).mpr hbounds.2


noncomputable def orbitGramCoefficientKey (gram : Fin 2256) : Fin 995 :=
  ⟨(gramOrbitCoefficientOrbit gram.val).toNat,
    orbitGramCoefficientOrbit_lt gram⟩

@[simp] theorem orbitGramCoefficientKey_val (gram : Fin 2256) :
    (orbitGramCoefficientKey gram).val =
      (gramOrbitCoefficientOrbit gram.val).toNat := rfl



theorem orbitGramCoefficientKey_cast (gram : Fin 2256) :
    gramOrbitCoefficientOrbit gram.val =
      ((orbitGramCoefficientKey gram).val : Int) := by
  have hindex : gram.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  have hfields := orbitGramRepresentativeFields_valid gram.val hindex
  let row := gramOrbitData[gram.val]
  have hrow : gramOrbitData[gram.val]? = some row := by
    simp [row, hindex]
  have hfield :
      gramOrbitCoefficientOrbit gram.val = orbitEntry row 2 := by
    simp [gramOrbitCoefficientOrbit, dataEntry,
      Array.getD_eq_getD_getElem?, hrow, orbitEntry]
  have hnonnegative : 0 ≤ gramOrbitCoefficientOrbit gram.val := by
    rw [hfield]
    simpa [row] using hfields.2.2.2.1.1
  exact (Int.toNat_of_nonneg hnonnegative).symm



theorem orbitGramSize_eq_incidence_mul_coefficientSize (gram : Fin 2256) :
    (gramOrbitSize gram.val).toNat =
      (gramOrbitIncidence gram.val).toNat *
        (dataEntry coefficientOrbitSizeData
          (orbitGramCoefficientKey gram).val 0).toNat := by
  have hindex : gram.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  let row := gramOrbitData[gram.val]
  have hrow : gramOrbitData[gram.val]? = some row := by
    simp [row, hindex]
  obtain ⟨_, hkey, hincidence, hsize, hcardinality⟩ :=
    orbitGramIncidenceRowCheck_sound gram.val row hrow
      (orbitGramIncidenceCheck_sound orbitGramIncidenceCheck_valid
        gram.val hindex)
  have hgramSize : gramOrbitSize gram.val = orbitEntry row 7 := by
    simp [gramOrbitSize, dataEntry, Array.getD_eq_getD_getElem?,
      hrow, orbitEntry]
  have hgramIncidence : gramOrbitIncidence gram.val = orbitEntry row 3 := by
    simp [gramOrbitIncidence, dataEntry, Array.getD_eq_getD_getElem?,
      hrow, orbitEntry]
  have hgramKey : gramOrbitCoefficientOrbit gram.val = orbitEntry row 2 := by
    simp [gramOrbitCoefficientOrbit, dataEntry,
      Array.getD_eq_getD_getElem?, hrow, orbitEntry]
  change
    (gramOrbitSize gram.val).toNat =
      (gramOrbitIncidence gram.val).toNat *
        (dataEntry coefficientOrbitSizeData
          (gramOrbitCoefficientOrbit gram.val).toNat 0).toNat
  rw [hgramSize, hgramIncidence, hgramKey, hcardinality,
    Int.toNat_mul hincidence.le hsize.le]





theorem orbitGramRepresentative_fiber_incidence_of_coefficient_card
    (pairKey : Fin 425 → Fin 425 → Fin 2256)
    (hbucket : ∀ (gram : Fin 2256) (pair : Fin 425 × Fin 425),
      pairKey pair.1 pair.2 = gram ↔
        pair ∈ MulAction.orbit OrbitSignedSymmetry
          (orbitGramRepresentative gram))
    (htransport : ∀ gram : Fin 2256,
      coefficientRepresentativeElement
          (orbitGramCoefficientKey gram).val ∈
        MulAction.orbit OrbitSignedSymmetry
          ((orbitBasis (orbitGramRepresentative gram).1)⁻¹ *
            orbitBasis (orbitGramRepresentative gram).2))
    (hcoefficientCard : ∀ coefficient : Fin 995,
      Fintype.card (MulAction.orbit OrbitSignedSymmetry
        (coefficientRepresentativeElement coefficient.val)) =
          (dataEntry coefficientOrbitSizeData coefficient.val 0).toNat)
    (gram : Fin 2256) :
    gramPairFiberCount orbitBasis pairKey gram
        (coefficientRepresentativeElement
          (orbitGramCoefficientKey gram).val) =
      (gramOrbitIncidence gram.val).toNat := by
  classical
  let representative := orbitGramRepresentative gram
  let product : constructedGammaZeroGroup :=
    (orbitBasis representative.1)⁻¹ * orbitBasis representative.2
  let coefficient :=
    coefficientRepresentativeElement (orbitGramCoefficientKey gram).val
  have horbits :
      MulAction.orbit OrbitSignedSymmetry coefficient =
        MulAction.orbit OrbitSignedSymmetry product :=
    MulAction.orbit_eq_iff.mpr (htransport gram)
  have hproductCard :
      Fintype.card (MulAction.orbit OrbitSignedSymmetry product) =
        (dataEntry coefficientOrbitSizeData
          (orbitGramCoefficientKey gram).val 0).toNat := by
    calc
      Fintype.card (MulAction.orbit OrbitSignedSymmetry product) =
          Fintype.card (MulAction.orbit OrbitSignedSymmetry coefficient) :=
        (Fintype.card_congr (Equiv.setCongr horbits)).symm
      _ = _ := hcoefficientCard (orbitGramCoefficientKey gram)
  have hcardinality :
      Fintype.card (MulAction.orbit OrbitSignedSymmetry representative) =
        (gramOrbitIncidence gram.val).toNat *
          Fintype.card (MulAction.orbit OrbitSignedSymmetry product) := by
    rw [orbitGramRepresentative_orbit_card gram, hproductCard]
    exact orbitGramSize_eq_incidence_mul_coefficientSize gram
  exact gramPairFiberCount_eq_incidence_of_orbit
    (H := OrbitSignedSymmetry)
    orbitBasis pairKey
    (signedPairProduct_equivariant orbitBasis orbitSymmetry_basis_action)
    representative gram (hbucket gram) coefficient (htransport gram)
    (gramOrbitIncidence gram.val).toNat hcardinality



theorem orbitGramPairFiberCount_eq_zero_of_not_mem
    (pairKey : Fin 425 → Fin 425 → Fin 2256)
    (representative : Fin 425 × Fin 425)
    (gram : Fin 2256)
    (hbucket : ∀ pair : Fin 425 × Fin 425,
      pairKey pair.1 pair.2 = gram ↔
        pair ∈ MulAction.orbit OrbitSignedSymmetry representative)
    (hequivariant : ∀ symmetry : OrbitSignedSymmetry,
      ∀ pair : Fin 425 × Fin 425,
        (orbitBasis (symmetry • pair).1)⁻¹ *
            orbitBasis (symmetry • pair).2 =
          symmetry • ((orbitBasis pair.1)⁻¹ * orbitBasis pair.2))
    (coefficient : constructedGammaZeroGroup)
    (hcoefficient : coefficient ∉ MulAction.orbit OrbitSignedSymmetry
      ((orbitBasis representative.1)⁻¹ * orbitBasis representative.2)) :
    gramPairFiberCount orbitBasis pairKey gram coefficient = 0 := by
  classical
  letI : DecidableEq (Fin 2256) := Classical.decEq _
  unfold gramPairFiberCount
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨pair, hpair⟩
  have hpair' := Finset.mem_filter.mp hpair
  have hbucket' := (hbucket pair).mp hpair'.2.1
  obtain ⟨symmetry, hsymmetry⟩ :=
    MulAction.mem_orbit_iff.mp hbucket'
  apply hcoefficient
  refine MulAction.mem_orbit_iff.mpr ⟨symmetry, ?_⟩
  rw [← hequivariant]
  simpa [hsymmetry] using hpair'.2.2




theorem orbitGramRepresentative_fibers_of_orbits
    (pairKey : Fin 425 → Fin 425 → Fin 2256)
    (coefficientKey : Fin 2256 → Fin 995)
    (representative : Fin 2256 → Fin 425 × Fin 425)
    (hcoefficientKey : ∀ gram : Fin 2256,
      gramOrbitCoefficientOrbit gram.val =
        ((coefficientKey gram).val : Int))
    (hbucket : ∀ (gram : Fin 2256) (pair : Fin 425 × Fin 425),
      pairKey pair.1 pair.2 = gram ↔
        pair ∈ MulAction.orbit OrbitSignedSymmetry (representative gram))
    (hequivariant : ∀ symmetry : OrbitSignedSymmetry,
      ∀ pair : Fin 425 × Fin 425,
        (orbitBasis (symmetry • pair).1)⁻¹ *
            orbitBasis (symmetry • pair).2 =
          symmetry • ((orbitBasis pair.1)⁻¹ * orbitBasis pair.2))
    (htransport : ∀ gram : Fin 2256,
      coefficientRepresentativeElement (coefficientKey gram).val ∈
        MulAction.orbit OrbitSignedSymmetry
          ((orbitBasis (representative gram).1)⁻¹ *
            orbitBasis (representative gram).2))
    (hincidence : ∀ gram : Fin 2256,
      gramPairFiberCount orbitBasis pairKey gram
          (coefficientRepresentativeElement (coefficientKey gram).val) =
        (gramOrbitIncidence gram.val).toNat)
    (hdisjoint : ∀ first second : Fin 995,
      coefficientRepresentativeElement first.val ∈
        MulAction.orbit OrbitSignedSymmetry
          (coefficientRepresentativeElement second.val) →
      first = second)
    (coefficient : Fin 995) (gram : Fin 2256) :
    gramPairFiberCount orbitBasis pairKey gram
          (coefficientRepresentativeElement coefficient.val) =
      if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
      then (gramOrbitIncidence gram.val).toNat else 0 := by
  classical
  by_cases hkey : coefficientKey gram = coefficient
  · subst coefficient
    simp [hcoefficientKey, hincidence]
  · rw [if_neg]
    · apply orbitGramPairFiberCount_eq_zero_of_not_mem pairKey
        (representative gram) gram (hbucket gram) hequivariant
        (coefficientRepresentativeElement coefficient.val)
      intro hmember
      obtain ⟨first, hfirst⟩ :=
        MulAction.mem_orbit_iff.mp hmember
      obtain ⟨second, hsecond⟩ :=
        MulAction.mem_orbit_iff.mp (htransport gram)
      have hcoefficientOrbit :
          coefficientRepresentativeElement coefficient.val ∈
            MulAction.orbit OrbitSignedSymmetry
              (coefficientRepresentativeElement
                (coefficientKey gram).val) := by
        refine MulAction.mem_orbit_iff.mpr
          ⟨first * second⁻¹, ?_⟩
        rw [mul_smul, ← hsecond, inv_smul_smul, hfirst]
      exact hkey
        (hdisjoint coefficient (coefficientKey gram) hcoefficientOrbit).symm
    · intro hraw
      apply hkey
      apply Fin.ext
      exact_mod_cast (hcoefficientKey gram).symm.trans hraw






theorem orbitGramRepresentative_coeff_of_fibers
    (pairKey : Fin 425 → Fin 425 → Fin 2256)
    (hpairKey : ∀ left right,
      (pairKey left right).val = pairOrbit left.val right.val)
    (coefficient : Fin 995)
    (hfibers : ∀ gram : Fin 2256,
      gramPairFiberCount orbitBasis pairKey gram
          (coefficientRepresentativeElement coefficient.val) =
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
        then (gramOrbitIncidence gram.val).toNat else 0) :
    (fullGramExpansion orbitBasis
      (fun left right => (gramEntry left.val right.val : ℚ))).coeff
        (coefficientRepresentativeElement coefficient.val) =
      ∑ gram : Fin 2256,
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
        then ((gramOrbitIncidence gram.val).toNat : ℚ) *
          (gramOrbitCoefficient gram.val : ℚ)
        else 0 := by
  have hgram :
      (fun left right : Fin 425 =>
        (gramEntry left.val right.val : ℚ)) =
        fun left right =>
          (gramOrbitCoefficient (pairKey left right).val : ℚ) := by
    funext left right
    simp [gramEntry, hpairKey]
  rw [hgram]
  exact fullGramExpansion_coeff_eq_sum_orbit_incidence
    orbitBasis pairKey
    (fun gram : Fin 2256 => (gramOrbitCoefficient gram.val : ℚ))
    (fun gram : Fin 2256 => (gramOrbitIncidence gram.val).toNat)
    (fun gram : Fin 2256 =>
      gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int))
    (coefficientRepresentativeElement coefficient.val) hfibers






theorem orbitGramRepresentative_coeff_of_fibers_and_terms
    (pairKey : Fin 425 → Fin 425 → Fin 2256)
    (hpairKey : ∀ left right,
      (pairKey left right).val = pairOrbit left.val right.val)
    (coefficient : Fin 995)
    (hfibers : ∀ gram : Fin 2256,
      gramPairFiberCount orbitBasis pairKey gram
          (coefficientRepresentativeElement coefficient.val) =
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
        then (gramOrbitIncidence gram.val).toNat else 0)
    (hterms :
      (∑ gram : Fin 2256,
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
        then ((gramOrbitIncidence gram.val).toNat : ℚ) *
          (gramOrbitCoefficient gram.val : ℚ)
        else 0) = (coefficientOrbitTarget coefficient.val : ℚ)) :
    (fullGramExpansion orbitBasis
      (fun left right => (gramEntry left.val right.val : ℚ))).coeff
        (coefficientRepresentativeElement coefficient.val) =
      (coefficientOrbitTarget coefficient.val : ℚ) := by
  rw [orbitGramRepresentative_coeff_of_fibers
    pairKey hpairKey coefficient hfibers, hterms]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

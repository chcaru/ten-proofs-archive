


import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientOrbitDisjointness
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerValidation
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerData
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000



theorem signedAffineDescendingCoordinates_sound
    (symmetry : OrbitSymmetry) (row : Array Int)
    (hrow : isSymplecticRow row = true) :
    signedAffineDescendingCoordinates
        (symmetryData.getD symmetry.index.val #[]) row =
      gammaZeroDescendingCoordinates
        (symmetry • gammaZeroOfRow row) := by
  let raw := symmetryData.getD symmetry.index.val #[]
  have hnormalizer : isSignedNormalizerRow raw = true :=
    symmetryNormalizerRowChecks symmetry.index
  have htransport : isSymplecticRow (signedRowAction raw row) = true :=
    isSymplecticRow_signedRowAction hnormalizer hrow
  have hwidth : (signedRowAction raw row).size = 20 := by
    simp [signedRowAction]
  calc
    signedAffineDescendingCoordinates raw row =
        (signedRowAction raw row).toList.reverse :=
      signedAffineDescendingCoordinates_eq raw row
    _ = (gammaZeroCoordinates
          (gammaZeroOfRow (signedRowAction raw row))).reverse := by
      rw [gammaZeroCoordinates_gammaZeroOfRow htransport hwidth]
    _ = gammaZeroDescendingCoordinates
          (symmetry • gammaZeroOfRow row) := by
      rw [signedRowAction_sound hnormalizer hrow]
      rfl


theorem orbitSymmetry_raw_mem
    (symmetry : OrbitSymmetry) :
    symmetryData.getD symmetry.index.val #[] ∈ symmetryData.toList := by
  have hsize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  have hindex : symmetry.index.val < symmetryData.size := by
    simp [hsize]
  simp only [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hindex, Option.getD_some]
  exact Array.mem_toList_iff.mpr (Array.getElem_mem hindex)




theorem coefficientCanonicalWitnessRowCheck_sound
    (orbit : Nat) (witness : List Int)
    (representative inverse : Array Int)
    (hrepresentative : isSymplecticRow representative = true)
    (hinverse :
      rawProductCheck representative inverse orbitIdentityRow = true)
    (hcheck : coefficientCanonicalWitnessRowCheck orbit symmetryData.toList
      witness representative inverse = true) :
    ∃ canonical : List Int,
      coefficientCanonicalCoordinates (gammaZeroOfRow representative) =
          canonical.reverse ∧
        targetCoordinateCode canonical = witness.getD 1 0 := by
  let index := witness.getD 2 0
  let inversion := witness.getD 3 0
  let source := if inversion = 0 then representative else inverse
  let raw := symmetryData.getD index.toNat #[]
  let canonical := signedRowAction raw source
  change
    (decide (witness.length = 4) &&
      decide (witness.getD 0 0 = (orbit : Int)) &&
      decide (0 ≤ index ∧ index < (64 : Int)) &&
      decide (inversion = 0 ∨ inversion = 1) &&
      decide (representative.size = 20) &&
      decide (inverse.size = 20) &&
      decide
        (targetCoordinateCode canonical.toList = witness.getD 1 0) &&
      coefficientCanonicalImagesCheck canonical representative inverse
        symmetryData.toList) = true at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hindex⟩, hinversion⟩, _⟩, _⟩,
    hcode⟩, himages⟩ := hcheck
  have hindexNat : index.toNat < 64 := by omega
  let chosen : OrbitSymmetry := ⟨⟨index.toNat, hindexNat⟩⟩
  obtain ⟨hinverseValid, hinverseValue⟩ :=
    rawProductCheck_orbitIdentity_inverse hrepresentative hinverse
  have hchosen : raw = symmetryData.getD chosen.index.val #[] := rfl
  have hcandidate :
      ∃ symmetry : OrbitSignedSymmetry,
        gammaZeroDescendingCoordinates
          (symmetry • gammaZeroOfRow representative) =
            canonical.toList.reverse := by
    rcases hinversion with hzero | hone
    · refine ⟨(chosen, Multiplicative.ofAdd (0 : ZMod 2)), ?_⟩
      change
        gammaZeroDescendingCoordinates
            (orbitSymmetry chosen.index (gammaZeroOfRow representative)) =
          canonical.toList.reverse
      have hsound := signedAffineDescendingCoordinates_sound
        chosen representative hrepresentative
      rw [signedAffineDescendingCoordinates_eq] at hsound
      simpa [canonical, source, raw, hzero] using hsound.symm
    · refine ⟨(chosen, Multiplicative.ofAdd (1 : ZMod 2)), ?_⟩
      change
        gammaZeroDescendingCoordinates
            ((orbitSymmetry chosen.index (gammaZeroOfRow representative))⁻¹) =
          canonical.toList.reverse
      have hnotzero : inversion ≠ 0 := by omega
      have hsound := signedAffineDescendingCoordinates_sound
        chosen inverse hinverseValid
      rw [signedAffineDescendingCoordinates_eq] at hsound
      rw [hinverseValue] at hsound
      simp only [OrbitSymmetry.smul_def, map_inv] at hsound
      simpa [canonical, source, raw, hnotzero] using hsound.symm
  have hminimum : ∀ symmetry : OrbitSignedSymmetry,
      canonical.toList.reverse ≤
        gammaZeroDescendingCoordinates
          (symmetry • gammaZeroOfRow representative) := by
    intro symmetry
    have hentry := List.all_eq_true.mp himages
      (symmetryData.getD symmetry.1.index.val #[])
        (orbitSymmetry_raw_mem symmetry.1)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hentry
    obtain hparity | hparity :=
      zmodTwo_eq_zero_or_one symmetry.2.toAdd
    · rw [signedGroupAction_apply, hparity, if_pos rfl]
      change
        canonical.toList.reverse ≤
          gammaZeroDescendingCoordinates
            (symmetry.1 • gammaZeroOfRow representative)
      rw [← signedAffineDescendingCoordinates_sound
        symmetry.1 representative hrepresentative]
      exact hentry.1
    · rw [signedGroupAction_apply, hparity, if_neg (by decide)]
      have haction :
          (orbitSymmetry symmetry.1.index
            (gammaZeroOfRow representative))⁻¹ =
            symmetry.1 • gammaZeroOfRow inverse := by
        rw [hinverseValue]
        simp [OrbitSymmetry.smul_def]
      rw [haction, ← signedAffineDescendingCoordinates_sound
        symmetry.1 inverse hinverseValid]
      exact hentry.2
  exact ⟨canonical.toList,
    coefficientCanonicalCoordinates_eq_of_minimum
      (gammaZeroOfRow representative) canonical.toList.reverse
        hcandidate hminimum,
    hcode⟩




theorem coefficientCanonicalCoordinates_representative_of_row_check
    (orbit : Fin 995)
    (hrepresentative : isSymplecticRow
      (coefficientRepresentativeData.getD orbit.val #[]) = true)
    (hinverse : rawProductCheck
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[])
        orbitIdentityRow = true)
    (hrow : coefficientCanonicalWitnessRowCheck orbit.val
      symmetryData.toList
      (coefficientCanonicalWitnessData.getD orbit.val [])
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[]) = true) :
    ∃ canonical : List Int,
      coefficientCanonicalCoordinates
          (coefficientRepresentativeElement orbit.val) =
            canonical.reverse ∧
        targetCoordinateCode canonical =
          (coefficientCanonicalWitnessData.getD orbit.val []).getD 1 0 := by
  simpa [coefficientRepresentativeElement] using
    coefficientCanonicalWitnessRowCheck_sound orbit.val
      (coefficientCanonicalWitnessData.getD orbit.val [])
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[])
      hrepresentative hinverse hrow






theorem coefficientCanonicalCoordinates_representative_of_checks
    (orbit : Fin 995)
    (hcanonical : coefficientCanonicalWitnessRowsCheck symmetryData.toList 0
      coefficientCanonicalWitnessData coefficientRepresentativeData.toList
        coefficientInverseRepresentativeData.toList = true)
    (hwitness : coefficientCanonicalWitnessData.length = 995)
    (hinverseLength : coefficientInverseRepresentativeData.size = 995)
    (hrepresentative : isSymplecticRow
      (coefficientRepresentativeData.getD orbit.val #[]) = true)
    (hinverse : rawProductCheck
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[])
        orbitIdentityRow = true) :
    ∃ canonical : List Int,
      coefficientCanonicalCoordinates
          (coefficientRepresentativeElement orbit.val) =
            canonical.reverse ∧
        targetCoordinateCode canonical =
          (coefficientCanonicalWitnessData.getD orbit.val []).getD 1 0 := by
  have hindex : orbit.val < coefficientCanonicalWitnessData.length := by
    simp [hwitness]
  have hrepresentativeLength :
      coefficientCanonicalWitnessData.length =
        coefficientRepresentativeData.toList.length := by
    simp [hwitness, coefficientRepresentativeData_size]
  have hinversesLength :
      coefficientCanonicalWitnessData.length =
        coefficientInverseRepresentativeData.toList.length := by
    simp [hwitness, hinverseLength]
  have hrow := coefficientCanonicalWitnessRowsCheck_get
    symmetryData.toList coefficientCanonicalWitnessData
      coefficientRepresentativeData.toList
      coefficientInverseRepresentativeData.toList 0 orbit.val
      hindex hrepresentativeLength hinversesLength hcanonical
  have hrepresentativeIndex : orbit.val < coefficientRepresentativeData.size := by
    simp [coefficientRepresentativeData_size]
  have hinverseIndex : orbit.val < coefficientInverseRepresentativeData.size := by
    simp [hinverseLength]
  have hwitnessEntry :
      coefficientCanonicalWitnessData[orbit.val] =
        coefficientCanonicalWitnessData.getD orbit.val [] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hindex]
  have hrepresentativeEntry :
      coefficientRepresentativeData.toList[orbit.val] =
        coefficientRepresentativeData.getD orbit.val #[] := by
    simp [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hrepresentativeIndex]
  have hinverseEntry :
      coefficientInverseRepresentativeData.toList[orbit.val] =
        coefficientInverseRepresentativeData.getD orbit.val #[] := by
    simp [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hinverseIndex]
  simp only [Nat.zero_add, hwitnessEntry, hrepresentativeEntry,
    hinverseEntry] at hrow
  simpa [coefficientRepresentativeElement] using
    coefficientCanonicalWitnessRowCheck_sound orbit.val
      (coefficientCanonicalWitnessData.getD orbit.val [])
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[])
      hrepresentative hinverse hrow

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

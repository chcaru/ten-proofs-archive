
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedRow
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedWitnessValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedActionImageSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem coefficientCanonicalPackedImagesCheck_sound
    (orbit : Fin 995)
    (hpacked : coefficientCanonicalPackedImagesCheck
      ((canonicalPackedWitnessRecord orbit).getD 1 0).toNat
      ((canonicalPackedWitnessRecord orbit).getD 2 0).toNat
      ((canonicalPackedWitnessRecord orbit).getD 3 0).toNat
      canonicalPackedActionData = true) :
    coefficientCanonicalImagesCheck
      (canonicalPackedWitnessCanonicalRow
        (coefficientCanonicalWitnessData.getD orbit.val [])
        (coefficientRepresentativeData.getD orbit.val #[])
        (coefficientInverseRepresentativeData.getD orbit.val #[]))
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[])
      symmetryData.toList = true := by
  let packed := canonicalPackedWitnessRecord orbit
  let witness := coefficientCanonicalWitnessData.getD orbit.val []
  let representative := coefficientRepresentativeData.getD orbit.val #[]
  let inverse := coefficientInverseRepresentativeData.getD orbit.val #[]
  let canonical :=
    canonicalPackedWitnessCanonicalRow witness representative inverse
  obtain ⟨hpackedLength, hwitnessLength, hpackedOrbit, hwitnessOrbit,
      hsymmetry, hinversion, hrepresentativeSize, hinverseSize,
      hcanonicalBounds, hrepresentativeBounds, hinverseBounds,
      hcanonicalNonnegative, hrepresentativeNonnegative,
      hinverseNonnegative, hcanonicalWitness, hcanonicalPacking,
      hrepresentativePacking, hinversePacking⟩ :=
    canonicalPackedWitnessRecord_sound orbit
  change coefficientCanonicalImagesCheck canonical representative inverse
    symmetryData.toList = true
  unfold coefficientCanonicalImagesCheck
  apply List.all_eq_true.mpr
  intro symmetry hmember
  obtain ⟨index, hindex, rfl⟩ :=
    Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hmember)
  have hsymmetrySize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  have hindex64 : index < 64 := by
    simpa [hsymmetrySize] using hindex
  let signedSymmetry : Fin 64 := ⟨index, hindex64⟩
  have hactionIndex : index < canonicalPackedActionData.length := by
    simpa [canonicalPackedActionData_length] using hindex64
  let actionRecord := canonicalPackedActionData.getD index []
  have hactionMember : actionRecord ∈ canonicalPackedActionData := by
    simp [actionRecord, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hactionIndex]
  have haction :=
    (List.all_eq_true.mp hpacked) actionRecord hactionMember
  have hactionRecord := canonicalPackedActionRowsCheck_get
    canonicalPackedActionData 0 index hactionIndex
      canonicalPackedActionRowsCheck_valid
  simp only [canonicalPackedActionRecordCheck,
    Bool.and_eq_true, decide_eq_true_eq, Nat.zero_add] at hactionRecord
  have hactionLength : actionRecord.length = 2 :=
    hactionRecord.1.1.1
  obtain ⟨stored, tail, hrecord⟩ := List.exists_cons_of_ne_nil
    (show actionRecord ≠ [] by
      intro hnil
      simp [hnil] at hactionLength)
  obtain ⟨code, extra, htail⟩ := List.exists_cons_of_ne_nil
    (show tail ≠ [] by
      intro hnil
      simp [hrecord, hnil] at hactionLength)
  have hextra : extra = [] := by
    simpa [hrecord, htail] using hactionLength
  have hshape : actionRecord = [stored, code] := by
    simp [hrecord, htail, hextra]
  have hcode : code.toNat = canonicalPackedActionCode index := by
    change
      code.toNat =
        ((canonicalPackedActionData.getD index []).getD 1 0).toNat
    change code.toNat = (actionRecord.getD 1 0).toNat
    rw [hshape]
    rfl
  have hrawSymmetry :
      symmetryData.getD index #[] = symmetryData[index] := by
    simp [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hindex]
  simp only [coefficientCanonicalPackedImagesCheck,
    List.all_eq_true] at hpacked
  rw [hshape] at haction
  simp only [Bool.and_eq_true] at haction
  rw [hcode] at haction
  have hcanonicalSize : canonical.size = 20 := by
    simp [canonical, canonicalPackedWitnessCanonicalRow, signedRowAction]
  have hcanonicalCoordinate (coordinate : Nat)
      (hcoordinate : coordinate < 20) :
      canonicalPackedCoordinate
          (packed.getD 1 0).toNat coordinate =
        signedAffineCoordinate
          (symmetryData.getD (witness.getD 2 0).toNat #[])
          (if witness.getD 3 0 = 0 then representative else inverse)
          coordinate := by
    rw [hcanonicalPacking]
    rw [canonicalPackedCoordinate_eq_getD canonical coordinate
      (by simpa [hcanonicalSize] using hcoordinate)
      (canonicalPackedCoordinateBounds_sound canonical hcanonicalBounds)]
    exact (signedAffineCoordinate_eq_signedRowAction_getD
      (symmetryData.getD (witness.getD 2 0).toNat #[])
      (if witness.getD 3 0 = 0 then representative else inverse)
      coordinate hcoordinate).symm
  have hrepresentativeImage (coordinate : Nat)
      (hcoordinate : coordinate < 20) :
      canonicalPackedActionCoordinate
          (canonicalPackedActionCode index)
          (packed.getD 2 0).toNat coordinate =
        signedAffineCoordinate (symmetryData.getD index #[])
          representative coordinate := by
    rw [hrepresentativePacking]
    exact canonicalPackedActionImageCoordinate_sound
      signedSymmetry representative hrepresentativeSize
      hrepresentativeBounds ⟨coordinate, hcoordinate⟩
  have hinverseImage (coordinate : Nat)
      (hcoordinate : coordinate < 20) :
      canonicalPackedActionCoordinate
          (canonicalPackedActionCode index)
          (packed.getD 3 0).toNat coordinate =
        signedAffineCoordinate (symmetryData.getD index #[])
          inverse coordinate := by
    rw [hinversePacking]
    exact canonicalPackedActionImageCoordinate_sound
      signedSymmetry inverse hinverseSize hinverseBounds
      ⟨coordinate, hcoordinate⟩
  simp only [Bool.and_eq_true]
  constructor
  · apply decide_eq_true
    change
      (signedRowAction
        (symmetryData.getD (witness.getD 2 0).toNat #[])
        (if witness.getD 3 0 = 0 then representative else inverse)).toList.reverse ≤
          signedAffineDescendingCoordinates symmetryData[index]
            representative
    rw [← hrawSymmetry]
    exact canonicalPackedCoordinateLE_sound
      (packed.getD 1 0).toNat (canonicalPackedActionCode index)
      (packed.getD 2 0).toNat
      (symmetryData.getD (witness.getD 2 0).toNat #[])
      (if witness.getD 3 0 = 0 then representative else inverse)
      (symmetryData.getD index #[]) representative
      hcanonicalCoordinate hrepresentativeImage haction.1
  · apply decide_eq_true
    change
      (signedRowAction
        (symmetryData.getD (witness.getD 2 0).toNat #[])
        (if witness.getD 3 0 = 0 then representative else inverse)).toList.reverse ≤
          signedAffineDescendingCoordinates symmetryData[index]
            inverse
    rw [← hrawSymmetry]
    exact canonicalPackedCoordinateLE_sound
      (packed.getD 1 0).toNat (canonicalPackedActionCode index)
      (packed.getD 3 0).toNat
      (symmetryData.getD (witness.getD 2 0).toNat #[])
      (if witness.getD 3 0 = 0 then representative else inverse)
      (symmetryData.getD index #[]) inverse
      hcanonicalCoordinate hinverseImage haction.2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

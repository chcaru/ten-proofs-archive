
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedRow
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedActionValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedWitnessValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedTargetCode
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedImagesSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option linter.style.setOption false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem coefficientCanonicalWitnessRowCheck_of_packed_images
    (orbit : Fin 995)
    (hpacked :
      coefficientCanonicalPackedImagesCheck
        ((canonicalPackedWitnessRecord orbit).getD 1 0).toNat
        ((canonicalPackedWitnessRecord orbit).getD 2 0).toNat
        ((canonicalPackedWitnessRecord orbit).getD 3 0).toNat
        canonicalPackedActionData = true) :
    coefficientCanonicalWitnessRowCheck orbit.val symmetryData.toList
      (coefficientCanonicalWitnessData.getD orbit.val [])
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[]) = true := by
  have hmetadata := canonicalPackedWitnessRecord_sound orbit
  dsimp at hmetadata
  obtain ⟨hpackedLength, hwitnessLength, hpackedOrbit, hwitnessOrbit,
    hsymmetry, hparity, hrepresentativeSize, hinverseSize,
    hcanonicalBounds, hrepresentativeBounds, hinverseBounds,
    hcanonicalNonneg, hrepresentativeNonneg, hinverseNonneg,
    hcanonicalWitnessCode, hcanonicalCode,
    hrepresentativeCode, hinverseCode⟩ := hmetadata
  let witness := coefficientCanonicalWitnessData.getD orbit.val []
  let representative := coefficientRepresentativeData.getD orbit.val #[]
  let inverse := coefficientInverseRepresentativeData.getD orbit.val #[]
  let canonical :=
    canonicalPackedWitnessCanonicalRow witness representative inverse
  have hcode : targetCoordinateCode canonical.toList = witness.getD 1 0 := by
    calc
      targetCoordinateCode canonical.toList =
          (canonicalPackedRow canonical : Nat) := by
            symm
            exact canonicalPackedRow_eq_targetCoordinateCode
              canonical hcanonicalBounds
      _ = (((canonicalPackedWitnessRecord orbit).getD 1 0).toNat : Nat) := by
            exact_mod_cast hcanonicalCode.symm
      _ = (canonicalPackedWitnessRecord orbit).getD 1 0 := by
            exact Int.toNat_of_nonneg hcanonicalNonneg
      _ = witness.getD 1 0 := hcanonicalWitnessCode
  have himages := coefficientCanonicalPackedImagesCheck_sound orbit hpacked
  unfold coefficientCanonicalWitnessRowCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨hwitnessLength, hwitnessOrbit, hsymmetry.1, hsymmetry.2, hparity,
    hrepresentativeSize, hinverseSize, hcode, himages⟩

theorem coefficientCanonicalWitnessRowCheck_of_packed
    (orbit : Fin 995)
    (hpacked : coefficientCanonicalPackedWitnessRowCheck
      (canonicalPackedWitnessRecord orbit) = true) :
    coefficientCanonicalWitnessRowCheck orbit.val symmetryData.toList
      (coefficientCanonicalWitnessData.getD orbit.val [])
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[]) = true := by
  have hmetadata := canonicalPackedWitnessRecord_sound orbit
  dsimp at hmetadata
  obtain ⟨first, canonical, representative, inverse, hshape⟩ :=
    List.length_eq_four.mp hmetadata.1
  apply coefficientCanonicalWitnessRowCheck_of_packed_images orbit
  rw [hshape] at hpacked ⊢
  simpa [coefficientCanonicalPackedWitnessRowCheck] using hpacked

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

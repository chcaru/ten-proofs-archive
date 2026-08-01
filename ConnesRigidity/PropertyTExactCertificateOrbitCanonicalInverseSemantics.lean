
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerCoefficientSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem coefficientCanonicalRepresentative_valid_and_inverse
    (orbit : Fin 995) :
    isSymplecticRow
        (coefficientRepresentativeData.getD orbit.val #[]) = true ∧
      rawProductCheck
        (coefficientRepresentativeData.getD orbit.val #[])
        (coefficientInverseRepresentativeData.getD orbit.val #[])
        orbitIdentityRow = true := by
  let rows := coefficientRepresentativeData.toList
  let inverses := coefficientInverseRepresentativeData.toList
  let sizes := coefficientOrbitSizeData.toList
  let permutations := orbitPermutationRepresentatives symmetryData.toList
  have hindex : orbit.val < rows.length := by
    simp [rows, coefficientRepresentativeData_size]
  have hlength := (orbitCoefficientMaskStabilizerRowsCheck_lengths
    permutations rows inverses sizes
    orbitCoefficientMaskStabilizerRowsCheck_valid).1
  have hvalid := orbitCoefficientInverseRowsCheck_get rows inverses
    orbit.val hindex hlength orbitCoefficientInverseRowsCheck_valid
  have hrowIndex : orbit.val < coefficientRepresentativeData.size := by
    simpa [rows] using hindex
  have hinverseList : orbit.val < inverses.length := by
    rw [← hlength]
    exact hindex
  have hinverseIndex : orbit.val < coefficientInverseRepresentativeData.size := by
    simpa [inverses] using hinverseList
  simpa [rows, inverses, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hrowIndex,
    Array.getElem?_eq_getElem hinverseIndex] using hvalid

theorem coefficientCanonicalRepresentative_valid (orbit : Fin 995) :
    isSymplecticRow
      (coefficientRepresentativeData.getD orbit.val #[]) = true :=
  (coefficientCanonicalRepresentative_valid_and_inverse orbit).1

theorem coefficientCanonicalRepresentative_inverse (orbit : Fin 995) :
    rawProductCheck
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[])
      orbitIdentityRow = true :=
  (coefficientCanonicalRepresentative_valid_and_inverse orbit).2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

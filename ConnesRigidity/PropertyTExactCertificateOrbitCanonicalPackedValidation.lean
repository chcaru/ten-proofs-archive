


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch00
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch01
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch02
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch03
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch04
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch05
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch06
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch07
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch08
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidations.Batch09
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedRowSoundness









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.setOption false

private theorem canonicalPackedWitnessRow_of_chunk
    (orbit : Fin 995) (start count : Nat)
    (hlower : start ≤ orbit.val)
    (hupper : orbit.val < start + count)
    (hchunk : coefficientCanonicalPackedWitnessRowsCheck
      canonicalPackedActionData
      ((canonicalPackedWitnessData.drop start).take count) = true) :
    coefficientCanonicalPackedWitnessRowCheck
      (canonicalPackedWitnessData.getD orbit.val []) = true := by
  have hglobal : orbit.val < canonicalPackedWitnessData.length := by
    rw [canonicalPackedWitnessData_length]
    exact orbit.isLt
  have hlocal : orbit.val - start <
      ((canonicalPackedWitnessData.drop start).take count).length := by
    simp [List.length_take, List.length_drop,
      canonicalPackedWitnessData_length]
    omega
  have hrow := coefficientCanonicalPackedWitnessRowsCheck_get
    canonicalPackedActionData
    ((canonicalPackedWitnessData.drop start).take count)
    (orbit.val - start) hlocal hchunk
  have helement :
      ((canonicalPackedWitnessData.drop start).take count)[orbit.val - start] =
        canonicalPackedWitnessData[orbit.val] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    omega
  rw [helement] at hrow
  rw [List.getD_eq_getElem _ [] hglobal]
  split at hrow <;>
    simp_all [coefficientCanonicalPackedWitnessRowCheck]


theorem coefficientCanonicalPackedWitnessRowCheck_valid
    (orbit : Fin 995) :
    coefficientCanonicalPackedWitnessRowCheck
      (canonicalPackedWitnessRecord orbit) = true := by
  change coefficientCanonicalPackedWitnessRowCheck
    (canonicalPackedWitnessData.getD orbit.val []) = true
  by_cases h00 : orbit.val < 100
  · apply canonicalPackedWitnessRow_of_chunk orbit 0 100
    · omega
    · omega
    · exact coefficientCanonicalPackedWitnessBatch00
  ·
    by_cases h01 : orbit.val < 200
    · apply canonicalPackedWitnessRow_of_chunk orbit 100 100
      · omega
      · omega
      · exact coefficientCanonicalPackedWitnessBatch01
    ·
      by_cases h02 : orbit.val < 300
      · apply canonicalPackedWitnessRow_of_chunk orbit 200 100
        · omega
        · omega
        · exact coefficientCanonicalPackedWitnessBatch02
      ·
        by_cases h03 : orbit.val < 400
        · apply canonicalPackedWitnessRow_of_chunk orbit 300 100
          · omega
          · omega
          · exact coefficientCanonicalPackedWitnessBatch03
        ·
          by_cases h04 : orbit.val < 500
          · apply canonicalPackedWitnessRow_of_chunk orbit 400 100
            · omega
            · omega
            · exact coefficientCanonicalPackedWitnessBatch04
          ·
            by_cases h05 : orbit.val < 600
            · apply canonicalPackedWitnessRow_of_chunk orbit 500 100
              · omega
              · omega
              · exact coefficientCanonicalPackedWitnessBatch05
            ·
              by_cases h06 : orbit.val < 700
              · apply canonicalPackedWitnessRow_of_chunk orbit 600 100
                · omega
                · omega
                · exact coefficientCanonicalPackedWitnessBatch06
              ·
                by_cases h07 : orbit.val < 800
                · apply canonicalPackedWitnessRow_of_chunk orbit 700 100
                  · omega
                  · omega
                  · exact coefficientCanonicalPackedWitnessBatch07
                ·
                  by_cases h08 : orbit.val < 900
                  · apply canonicalPackedWitnessRow_of_chunk orbit 800 100
                    · omega
                    · omega
                    · exact coefficientCanonicalPackedWitnessBatch08
                  ·
                    apply canonicalPackedWitnessRow_of_chunk orbit 900 100
                    · omega
                    · omega
                    · exact coefficientCanonicalPackedWitnessBatch09



theorem coefficientCanonicalWitnessRowCheck_valid
    (orbit : Fin 995) :
    coefficientCanonicalWitnessRowCheck
      orbit.val symmetryData.toList
      (coefficientCanonicalWitnessData.getD orbit.val [])
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[]) = true :=
  coefficientCanonicalWitnessRowCheck_of_packed orbit
    (coefficientCanonicalPackedWitnessRowCheck_valid orbit)

end ConnesRigidity.AffineSymplecticOrbitCertificate

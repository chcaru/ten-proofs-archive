
import ConnesRigidity.PropertyTExactCertificateOrbitRadixPackedBridge

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

theorem orbitRadixGramRecordValue_eq_reducedGramEncoding_of_dense
    (row : Fin 424)
    (hactual :
      (radixDenseReducedGramRowData.getD row.val []).drop 1 =
        (List.range 424).map fun column =>
          gramEntry (row.val + 1) (column + 1)) :
    orbitRadixRecordValue radixEncodedGramData row.val =
      orbitRadixReducedGramEncoding row.val := by
  have hcheck := orbitRadixGramRowCheck_valid row
  cases hdense : radixDenseReducedGramRowData[row.val]? with
  | none => simp [orbitRadixGramRowCheck, hdense] at hcheck
  | some dense =>
      cases dense with
      | nil => simp [orbitRadixGramRowCheck, hdense] at hcheck
      | cons stored entries =>
          cases hencoded : radixEncodedGramData[row.val]? with
          | none => simp [orbitRadixGramRowCheck, hdense, hencoded] at hcheck
          | some encodedRow =>
              cases encodedRow with
              | nil =>
                  simp [orbitRadixGramRowCheck, hdense, hencoded] at hcheck
              | cons storedEncoded remaining =>
                  cases remaining with
                  | nil =>
                      simp [orbitRadixGramRowCheck, hdense, hencoded] at hcheck
                  | cons encoded tail =>
                      cases tail with
                      | cons _ _ =>
                          simp [orbitRadixGramRowCheck, hdense, hencoded]
                            at hcheck
                      | nil =>
                          have hproperties := orbitRadixGramRowCheck_sound
                            row.val stored storedEncoded encoded entries
                            hdense hencoded hcheck
                          have hrecord :
                              orbitRadixRecordValue radixEncodedGramData
                                  row.val = encoded := by
                            unfold orbitRadixRecordValue
                            change
                              (((radixEncodedGramData[row.val]?).getD []).getD
                                1 0) = encoded
                            rw [hencoded]
                            rfl
                          have hdenseGet :
                              radixDenseReducedGramRowData.getD row.val [] =
                                stored :: entries := by
                            simp [List.getD_eq_getElem?_getD, hdense]
                          rw [hdenseGet] at hactual
                          simp only [List.drop_succ_cons, List.drop_zero]
                            at hactual
                          rw [hrecord, ← hproperties.2.2.2, hactual]
                          unfold orbitRadixDenseReducedGramEncoding
                            orbitRadixReducedGramEncoding
                          rw [List.foldr_map]

theorem orbitRadix_packed_identity_of_verified_dense
    (hdense : ∀ row : Fin 424,
      (radixDenseReducedGramRowData.getD row.val []).drop 1 =
        (List.range 424).map fun column =>
          gramEntry (row.val + 1) (column + 1))
    (row : Fin 424) :
    orbitRadixEncode
        ((List.finRange 424).map (orbitRadixComputedEntry row)) =
      congruenceInverseScale ^ 2 *
        orbitRadixEncode
          ((List.finRange 424).map fun column =>
            gramEntry (row.val + 1) (column.val + 1)) := by
  have hpacked := orbitRadix_packed_identity_of_checks
    orbitRadixInverseRowCheck_valid
    orbitRadixProductRowCheck_valid
    orbitRadixFinalRowCheck_valid
    orbitRadixInverseRowPairCheck_valid
    orbitRadixInverseColumnPairCheck_valid
    (fun index => orbitRadixGramRecordValue_eq_reducedGramEncoding_of_dense
      index (hdense index)) row
  rw [orbitRadixReducedGramEncoding_eq_encode] at hpacked
  rw [orbitRadix_finRange_map_val
    (entry := fun column => gramEntry (row.val + 1) (column + 1))]
  exact hpacked

theorem orbitRadix_integer_identity_of_verified_dense
    (hdense : ∀ row : Fin 424,
      (radixDenseReducedGramRowData.getD row.val []).drop 1 =
        (List.range 424).map fun column =>
          gramEntry (row.val + 1) (column + 1))
    (row column : Fin 424) :
    orbitRadixComputedEntry row column =
      congruenceInverseScale ^ 2 *
        gramEntry (row.val + 1) (column.val + 1) :=
  orbitRadix_integer_identity_of_packed
    (orbitRadix_packed_identity_of_verified_dense hdense)
    orbitRadix_matrix_difference_bound row column

end ConnesRigidity.AffineSymplecticOrbitCertificate

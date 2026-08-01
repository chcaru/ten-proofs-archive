


import ConnesRigidity.PropertyTExactCertificateOrbitRadixCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitRadixSoundness









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators




theorem orbitRadixBlockDotEncoded_eq_fin_sum
    (coefficients : List Int) (records : List (List Int)) :
    orbitRadixBlockDotEncoded coefficients records =
      ∑ index : Fin coefficients.length,
        coefficients.getD index.val 0 *
          orbitRadixRecordValue records index.val := by
  induction coefficients generalizing records with
  | nil => simp [orbitRadixBlockDotEncoded]
  | cons coefficient coefficients ih =>
      cases records with
      | nil => simp [orbitRadixBlockDotEncoded, orbitRadixRecordValue]
      | cons record records =>
          simp only [List.length_cons]
          rw [Fin.sum_univ_succ]
          simp only [orbitRadixBlockDotEncoded,
            orbitRadixRecordValue, Fin.val_zero,
            List.getD_cons_zero, Fin.val_succ,
            List.getD_cons_succ]
          rw [ih records]
          rfl


theorem orbitRadixRecordValue_drop
    (records : List (List Int)) (start index : Nat) :
    orbitRadixRecordValue (records.drop start) index =
      orbitRadixRecordValue records (start + index) := by
  simp [orbitRadixRecordValue, List.getD_eq_getElem?_getD,
    List.getElem?_drop]



theorem orbitRadixProductRowCheck_recordValue_eq_fin_sum
    (index : Nat) (column : Array Int) (row encoded : Int)
    (hcolumn : blockColumnData[index]? = some column)
    (hencoded : radixEncodedProductData[index]? = some [row, encoded])
    (hcheck : orbitRadixProductRowCheck index = true) :
    let block := (column.getD 1 0).toNat
    let localIndex := (column.getD 2 0).toNat
    encoded =
      ∑ offset : Fin (blockDimension block),
        blockGramEntryInt block localIndex offset.val *
          orbitRadixRecordValue radixEncodedInverseData
            (blockRowStart block + offset.val) := by
  dsimp
  obtain ⟨_, _, _, hlength, hdot⟩ :=
    orbitRadixProductRowCheck_sound index column row encoded
      hcolumn hencoded hcheck
  rw [← hdot, orbitRadixBlockDotEncoded_eq_fin_sum, hlength]
  apply Finset.sum_congr rfl
  intro offset _
  rw [orbitRadixRecordValue_drop]
  rfl



theorem orbitRadixProductRowCheck_encoded_eq_fin_sum
    (index : Nat) (column : Array Int) (row encoded : Int)
    (hcolumn : blockColumnData[index]? = some column)
    (hencoded : radixEncodedProductData[index]? = some [row, encoded])
    (hcheck : orbitRadixProductRowCheck index = true)
    (hinverse :
      ∀ offset : Fin (blockDimension (column.getD 1 0).toNat),
        orbitRadixRecordValue radixEncodedInverseData
            (blockRowStart (column.getD 1 0).toNat + offset.val) =
          orbitRadixEncode
            ((List.finRange 424).map fun other =>
              scaledCongruenceInverseEntry
                (blockRowStart (column.getD 1 0).toNat + offset.val)
                other.val)) :
    let block := (column.getD 1 0).toNat
    let localIndex := (column.getD 2 0).toNat
    encoded =
      ∑ offset : Fin (blockDimension block),
        blockGramEntryInt block localIndex offset.val *
          orbitRadixEncode
            ((List.finRange 424).map fun other =>
              scaledCongruenceInverseEntry
                (blockRowStart block + offset.val) other.val) := by
  dsimp
  rw [orbitRadixProductRowCheck_recordValue_eq_fin_sum
    index column row encoded hcolumn hencoded hcheck]
  apply Finset.sum_congr rfl
  intro offset _
  rw [hinverse offset]

end ConnesRigidity.AffineSymplecticOrbitCertificate

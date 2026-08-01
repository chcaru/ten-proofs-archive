
import ConnesRigidity.PropertyTExactCertificateOrbitRadixCheckers

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem scaledInversePairLookup_ne_zero_mem (key : Int) :
    ∀ (fields : List Int),
      scaledInversePairLookup key fields ≠ 0 →
        (key, scaledInversePairLookup key fields) ∈
          scaledInverseDecodePairs fields
  | [], h => (h rfl).elim
  | [_], h => (h rfl).elim
  | present :: value :: remaining, h => by
      by_cases hkey : present = key
      · subst present
        simp [scaledInversePairLookup, scaledInverseDecodePairs]
      · have hremaining : scaledInversePairLookup key remaining ≠ 0 := by
          simpa [scaledInversePairLookup, hkey] using h
        have hmember :=
          scaledInversePairLookup_ne_zero_mem key remaining hremaining
        simp [scaledInversePairLookup, scaledInverseDecodePairs, hkey,
          hmember]

theorem orbitRadixColumnPairLookup_eq_entry_of_checks
    (row column : Fin 424)
    (hrow : orbitRadixInverseRowPairCheck row.val = true)
    (hcolumn : orbitRadixInverseColumnPairCheck column.val = true) :
    orbitRadixColumnPairLookup column.val row.val =
      scaledCongruenceInverseEntry row.val column.val := by
  cases hrowData : scaledInverseRowData[row.val]? with
  | none => simp [orbitRadixInverseRowPairCheck, hrowData] at hrow
  | some rowData =>
      cases rowData with
      | nil => simp [orbitRadixInverseRowPairCheck, hrowData] at hrow
      | cons storedRow rowFields =>
          cases hcolumnData : scaledInverseColumnData[column.val]? with
          | none =>
              simp [orbitRadixInverseColumnPairCheck, hcolumnData] at hcolumn
          | some columnData =>
              cases columnData with
              | nil =>
                  simp [orbitRadixInverseColumnPairCheck, hcolumnData]
                    at hcolumn
              | cons storedColumn columnFields =>
                  have rowSound := orbitRadixInverseRowPairCheck_sound
                    row.val storedRow rowFields hrowData hrow
                  have columnSound := orbitRadixInverseColumnPairCheck_sound
                    column.val storedColumn columnFields hcolumnData hcolumn
                  have rowLookup :
                      scaledCongruenceInverseEntry row.val column.val =
                        scaledInversePairLookup (column.val : Int)
                          rowFields := by
                    unfold scaledCongruenceInverseEntry
                    change
                      scaledInversePairLookup (column.val : Int)
                        (((scaledInverseRowData[row.val]?).getD []).drop 1) = _
                    rw [hrowData]
                    rfl
                  have columnLookup :
                      orbitRadixColumnPairLookup column.val row.val =
                        scaledInversePairLookup (row.val : Int)
                          columnFields := by
                    unfold orbitRadixColumnPairLookup
                    change
                      scaledInversePairLookup (row.val : Int)
                        (((scaledInverseColumnData[column.val]?).getD []).drop 1) = _
                    rw [hcolumnData]
                    rfl
                  by_cases hentry :
                      scaledInversePairLookup (column.val : Int) rowFields = 0
                  · have htranspose :
                        scaledInversePairLookup (row.val : Int)
                          columnFields = 0 := by
                      by_contra hnonzero
                      have hmember := scaledInversePairLookup_ne_zero_mem
                        (row.val : Int) columnFields hnonzero
                      have hchecked :=
                        (List.all_eq_true.mp columnSound.2.2) _ hmember
                      have hequality :
                          scaledCongruenceInverseEntry row.val column.val =
                            scaledInversePairLookup (row.val : Int)
                              columnFields := by
                        simpa using of_decide_eq_true hchecked
                      rw [rowLookup, hentry] at hequality
                      exact hnonzero hequality.symm
                    rw [columnLookup, htranspose, rowLookup, hentry]
                  · have hmember := scaledInversePairLookup_ne_zero_mem
                      (column.val : Int) rowFields hentry
                    have hchecked :=
                      (List.all_eq_true.mp rowSound.2.2) _ hmember
                    have hequality :
                        orbitRadixColumnPairLookup column.val row.val =
                          scaledInversePairLookup (column.val : Int)
                            rowFields := by
                      simpa using of_decide_eq_true hchecked
                    exact hequality.trans rowLookup.symm

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

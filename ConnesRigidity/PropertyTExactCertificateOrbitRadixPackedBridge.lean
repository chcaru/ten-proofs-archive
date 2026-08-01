


import ConnesRigidity.PropertyTExactCertificateOrbitRadixBlockPartition
import ConnesRigidity.PropertyTExactCertificateOrbitRadixMatrixSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitRadixProductSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitRadixSparseSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitRadixTransposeSoundness










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators



theorem orbitRadixSparseProductSum_eq_pair_sum (entries : List Int) :
    orbitRadixSparseProductSum entries =
      ((scaledInverseDecodePairs entries).map fun pair =>
        pair.2 * orbitRadixRecordValue
          radixEncodedProductData pair.1.toNat).sum := by
  induction entries using scaledInverseDecodePairs.induct with
  | case1 key value remaining ih =>
      simp [orbitRadixSparseProductSum, scaledInverseDecodePairs, ih]
  | case2 entries hshort =>
      cases entries with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => rfl
          | cons second rest =>
              exact False.elim (hshort first second rest rfl)



theorem orbitRadixInverseRecordValue_eq_encode_of_checks
    (row : Fin 424)
    (hinverse : orbitRadixInverseRowCheck row.val = true)
    (hpairs : orbitRadixInverseRowPairCheck row.val = true) :
    orbitRadixRecordValue radixEncodedInverseData row.val =
      orbitRadixEncode
        ((List.finRange 424).map fun column =>
          scaledCongruenceInverseEntry row.val column.val) := by
  cases hsource : scaledInverseRowData[row.val]? with
  | none => simp [orbitRadixInverseRowCheck, hsource] at hinverse
  | some source =>
      cases source with
      | nil => simp [orbitRadixInverseRowCheck, hsource] at hinverse
      | cons sourceRow entries =>
          cases hencoded : radixEncodedInverseData[row.val]? with
          | none =>
              simp [orbitRadixInverseRowCheck, hsource, hencoded] at hinverse
          | some encodedRecord =>
              cases encodedRecord with
              | nil =>
                  simp [orbitRadixInverseRowCheck, hsource, hencoded]
                    at hinverse
              | cons encodedRow remaining =>
                  cases remaining with
                  | nil =>
                      simp [orbitRadixInverseRowCheck, hsource, hencoded]
                        at hinverse
                  | cons encoded tail =>
                      cases tail with
                      | cons _ _ =>
                          simp [orbitRadixInverseRowCheck, hsource, hencoded]
                            at hinverse
                      | nil =>
                          have hsorted :=
                            (orbitRadixInverseRowPairCheck_sound row.val
                              sourceRow entries hsource hpairs).2.1
                          simp only [orbitRadixInverseRowCheck, hsource,
                            hencoded, Bool.and_eq_true,
                            decide_eq_true_eq] at hinverse
                          have hrecord :
                              orbitRadixRecordValue radixEncodedInverseData
                                row.val = encoded := by
                            unfold orbitRadixRecordValue
                            change
                              (((radixEncodedInverseData[row.val]?).getD []).getD
                                1 0) = encoded
                            rw [hencoded]
                            rfl
                          have hentry (column : Nat) :
                              scaledCongruenceInverseEntry row.val column =
                                scaledInversePairLookup (column : Int)
                                  entries := by
                            unfold scaledCongruenceInverseEntry
                            change
                              scaledInversePairLookup (column : Int)
                                (((scaledInverseRowData[row.val]?).getD []).drop
                                  1) = _
                            rw [hsource]
                            rfl
                          have hcoordinates :
                              ((List.finRange 424).map fun column =>
                                scaledCongruenceInverseEntry row.val
                                  column.val) =
                              ((List.range 424).map fun column =>
                                scaledInversePairLookup (column : Int)
                                  entries) := by
                            rw [orbitRadix_finRange_map_val]
                            simp only [LawfulMonad.bind_pure_comp]
                            change (List.range 424).map
                              (scaledCongruenceInverseEntry row.val) =
                                ((List.range 424).map
                                  (fun column : Nat => (column : Int))).map
                                  (fun column : Int =>
                                    scaledInversePairLookup column entries)
                            rw [List.map_map]
                            apply List.map_congr_left
                            intro column _
                            exact hentry column
                          rw [hrecord, ← hinverse.2,
                            orbitRadixEncodeSparsePairs_eq_dense entries hsorted]
                          exact congrArg orbitRadixEncode hcoordinates.symm



theorem orbitRadixProductRecordValue_eq_block_sum_of_checks
    (block : Fin 28) (offset : Fin (blockDimension block.val))
    (hproduct : orbitRadixProductRowCheck
      (blockRowStart block.val + offset.val) = true)
    (hinverse : ∀ row : Fin 424,
      orbitRadixRecordValue radixEncodedInverseData row.val =
        orbitRadixEncode
          ((List.finRange 424).map fun column =>
            scaledCongruenceInverseEntry row.val column.val)) :
    orbitRadixRecordValue radixEncodedProductData
        (blockRowStart block.val + offset.val) =
      ∑ other : Fin (blockDimension block.val),
        blockGramEntryInt block.val offset.val other.val *
          orbitRadixEncode
            ((List.finRange 424).map fun column =>
              scaledCongruenceInverseEntry
                (blockRowStart block.val + other.val) column.val) := by
  let index : Fin 424 :=
    ⟨blockRowStart block.val + offset.val,
      orbitBlockRowStart_add_lt block offset⟩
  change orbitRadixProductRowCheck index.val = true at hproduct
  cases hcolumn : blockColumnData[index.val]? with
  | none => simp [orbitRadixProductRowCheck, hcolumn] at hproduct
  | some column =>
      cases hencoded : radixEncodedProductData[index.val]? with
      | none =>
          simp [orbitRadixProductRowCheck, hcolumn, hencoded] at hproduct
      | some record =>
          cases record with
          | nil =>
              simp [orbitRadixProductRowCheck, hcolumn, hencoded] at hproduct
          | cons storedRow remaining =>
              cases remaining with
              | nil =>
                  simp [orbitRadixProductRowCheck, hcolumn, hencoded]
                    at hproduct
              | cons encoded rest =>
                  cases rest with
                  | cons _ _ =>
                      simp [orbitRadixProductRowCheck, hcolumn, hencoded]
                        at hproduct
                  | nil =>
                      have hblock :
                          (column.getD 1 0).toNat = block.val := by
                        have hcolumnGet :
                            blockColumnData.getD index.val #[] = column := by
                          rw [Array.getD_eq_getD_getElem?, hcolumn]
                          rfl
                        have hmetadata := (orbitBlock_metadata block offset).1
                        unfold blockOfColumn dataEntry at hmetadata
                        change ((blockColumnData.getD index.val #[]).getD
                          1 0).toNat = block.val at hmetadata
                        rw [hcolumnGet] at hmetadata
                        exact hmetadata
                      have hoffset :
                          (column.getD 2 0).toNat = offset.val := by
                        have hcolumnGet :
                            blockColumnData.getD index.val #[] = column := by
                          rw [Array.getD_eq_getD_getElem?, hcolumn]
                          rfl
                        have hmetadata := (orbitBlock_metadata block offset).2
                        unfold blockOffsetOfColumn dataEntry at hmetadata
                        change ((blockColumnData.getD index.val #[]).getD
                          2 0).toNat = offset.val at hmetadata
                        rw [hcolumnGet] at hmetadata
                        exact hmetadata
                      have hrecord :
                          orbitRadixRecordValue radixEncodedProductData
                            index.val = encoded := by
                        unfold orbitRadixRecordValue
                        change
                          (((radixEncodedProductData[index.val]?).getD []).getD
                            1 0) = encoded
                        rw [hencoded]
                        rfl
                      rw [show blockRowStart block.val + offset.val =
                        index.val from rfl, hrecord]
                      have hencodedSum :=
                        orbitRadixProductRowCheck_recordValue_eq_fin_sum
                          index.val column storedRow encoded hcolumn hencoded
                          hproduct
                      dsimp at hencodedSum
                      rw [hblock, hoffset] at hencodedSum
                      rw [hencodedSum]
                      apply Finset.sum_congr rfl
                      intro other _
                      exact congrArg
                        (fun value : Int =>
                          blockGramEntryInt block.val offset.val other.val *
                            value)
                        (hinverse
                          ⟨blockRowStart block.val + other.val,
                            orbitBlockRowStart_add_lt block other⟩)




theorem orbitRadixComputedRowEncoding_eq_block_sum (row : Fin 424) :
    orbitRadixEncode
        ((List.finRange 424).map (orbitRadixComputedEntry row)) =
      ∑ block : Fin 28,
        ∑ offset : Fin (blockDimension block.val),
          scaledCongruenceInverseEntry
              (blockRowStart block.val + offset.val) row.val *
            ∑ other : Fin (blockDimension block.val),
              blockGramEntryInt block.val offset.val other.val *
                orbitRadixEncode
                  ((List.finRange 424).map fun column =>
                    scaledCongruenceInverseEntry
                      (blockRowStart block.val + other.val)
                      column.val) := by
  have hblocks := orbitRadixEncode_fin_weighted_sum
    (List.finRange 424)
    (fun _ : Fin 28 => (1 : ℤ))
    (fun block column => orbitRadixBlockComputedEntry block.val row column)
  simp only [one_mul] at hblocks
  rw [show orbitRadixComputedEntry row =
    (fun column => ∑ block : Fin 28,
      orbitRadixBlockComputedEntry block.val row column) by rfl, hblocks]
  apply Finset.sum_congr rfl
  intro block _
  have hoffsets := orbitRadixEncode_fin_weighted_sum
    (List.finRange 424)
    (fun offset : Fin (blockDimension block.val) =>
      scaledCongruenceInverseEntry
        (blockRowStart block.val + offset.val) row.val)
    (fun offset column =>
      ∑ other : Fin (blockDimension block.val),
        blockGramEntryInt block.val offset.val other.val *
          scaledCongruenceInverseEntry
            (blockRowStart block.val + other.val) column.val)
  rw [show (fun column => orbitRadixBlockComputedEntry block.val row column) =
    (fun column => ∑ offset : Fin (blockDimension block.val),
      scaledCongruenceInverseEntry
        (blockRowStart block.val + offset.val) row.val *
        ∑ other : Fin (blockDimension block.val),
          blockGramEntryInt block.val offset.val other.val *
            scaledCongruenceInverseEntry
              (blockRowStart block.val + other.val) column.val) by rfl,
    hoffsets]
  apply Finset.sum_congr rfl
  intro offset _
  congr 1
  exact orbitRadixEncode_fin_weighted_sum
    (List.finRange 424)
    (fun other : Fin (blockDimension block.val) =>
      blockGramEntryInt block.val offset.val other.val)
    (fun other column =>
      scaledCongruenceInverseEntry
        (blockRowStart block.val + other.val) column.val)





theorem orbitRadix_packed_identity_of_checks
    (hinverse : ∀ row : Fin 424,
      orbitRadixInverseRowCheck row.val = true)
    (hproduct : ∀ row : Fin 424,
      orbitRadixProductRowCheck row.val = true)
    (hfinal : ∀ row : Fin 424,
      orbitRadixFinalRowCheck row.val = true)
    (hrowpairs : ∀ row : Fin 424,
      orbitRadixInverseRowPairCheck row.val = true)
    (hcolumnpairs : ∀ row : Fin 424,
      orbitRadixInverseColumnPairCheck row.val = true)
    (hgram : ∀ row : Fin 424,
      orbitRadixRecordValue radixEncodedGramData row.val =
        orbitRadixReducedGramEncoding row.val)
    (row : Fin 424) :
    orbitRadixEncode
        ((List.finRange 424).map (orbitRadixComputedEntry row)) =
      congruenceInverseScale ^ 2 *
        orbitRadixReducedGramEncoding row.val := by
  have hinverseMeaning (index : Fin 424) :
      orbitRadixRecordValue radixEncodedInverseData index.val =
        orbitRadixEncode
          ((List.finRange 424).map fun column =>
            scaledCongruenceInverseEntry index.val column.val) :=
    orbitRadixInverseRecordValue_eq_encode_of_checks index
      (hinverse index) (hrowpairs index)
  have hfinalRow := hfinal row
  cases hcolumn : scaledInverseColumnData[row.val]? with
  | none => simp [orbitRadixFinalRowCheck, hcolumn] at hfinalRow
  | some columnRecord =>
      cases columnRecord with
      | nil => simp [orbitRadixFinalRowCheck, hcolumn] at hfinalRow
      | cons storedColumn fields =>
          cases hencoded : radixEncodedGramData[row.val]? with
          | none =>
              simp [orbitRadixFinalRowCheck, hcolumn, hencoded] at hfinalRow
          | some encodedRecord =>
              cases encodedRecord with
              | nil =>
                  simp [orbitRadixFinalRowCheck, hcolumn, hencoded]
                    at hfinalRow
              | cons encodedRow remaining =>
                  cases remaining with
                  | nil =>
                      simp [orbitRadixFinalRowCheck, hcolumn, hencoded]
                        at hfinalRow
                  | cons encoded tail =>
                      cases tail with
                      | cons _ _ =>
                          simp [orbitRadixFinalRowCheck, hcolumn, hencoded]
                            at hfinalRow
                      | nil =>
                          have hsorted :=
                            (orbitRadixInverseColumnPairCheck_sound row.val
                              storedColumn fields hcolumn
                              (hcolumnpairs row)).2.1
                          simp only [orbitRadixFinalRowCheck, hcolumn,
                            hencoded, Bool.and_eq_true,
                            decide_eq_true_eq] at hfinalRow
                          have htarget :
                              encoded =
                                orbitRadixReducedGramEncoding row.val := by
                            have hrecord :
                                orbitRadixRecordValue radixEncodedGramData
                                  row.val = encoded := by
                              unfold orbitRadixRecordValue
                              change
                                (((radixEncodedGramData[row.val]?).getD []).getD
                                  1 0) = encoded
                              rw [hencoded]
                              rfl
                            exact hrecord.symm.trans (hgram row)
                          have hlookup (index : Fin 424) :
                              scaledInversePairLookup (index.val : Int)
                                fields =
                                scaledCongruenceInverseEntry
                                  index.val row.val := by
                            have hcolumnLookup :
                                orbitRadixColumnPairLookup
                                    row.val index.val =
                                  scaledInversePairLookup (index.val : Int)
                                    fields := by
                              unfold orbitRadixColumnPairLookup
                              change
                                scaledInversePairLookup (index.val : Int)
                                  (((scaledInverseColumnData[row.val]?).getD
                                    []).drop 1) = _
                              rw [hcolumn]
                              rfl
                            rw [← hcolumnLookup]
                            exact orbitRadixColumnPairLookup_eq_entry_of_checks
                              index row (hrowpairs index) (hcolumnpairs row)
                          calc
                            orbitRadixEncode
                                ((List.finRange 424).map
                                  (orbitRadixComputedEntry row)) =
                              ∑ block : Fin 28,
                                ∑ offset : Fin (blockDimension block.val),
                                  scaledCongruenceInverseEntry
                                      (blockRowStart block.val + offset.val)
                                      row.val *
                                    ∑ other : Fin (blockDimension block.val),
                                      blockGramEntryInt block.val offset.val
                                          other.val *
                                        orbitRadixEncode
                                          ((List.finRange 424).map fun column =>
                                            scaledCongruenceInverseEntry
                                              (blockRowStart block.val +
                                                other.val) column.val) :=
                                orbitRadixComputedRowEncoding_eq_block_sum row
                            _ = ∑ block : Fin 28,
                                  ∑ offset : Fin (blockDimension block.val),
                                    scaledCongruenceInverseEntry
                                        (blockRowStart block.val + offset.val)
                                        row.val *
                                      orbitRadixRecordValue
                                        radixEncodedProductData
                                        (blockRowStart block.val + offset.val) := by
                                  apply Finset.sum_congr rfl
                                  intro block _
                                  apply Finset.sum_congr rfl
                                  intro offset _
                                  congr 1
                                  exact (orbitRadixProductRecordValue_eq_block_sum_of_checks
                                    block offset
                                    (hproduct
                                      ⟨blockRowStart block.val + offset.val,
                                        orbitBlockRowStart_add_lt block offset⟩)
                                    hinverseMeaning).symm
                            _ = ∑ index : Fin 424,
                                  scaledCongruenceInverseEntry index.val row.val *
                                    orbitRadixRecordValue
                                      radixEncodedProductData index.val :=
                                orbitBlock_sum_eq_fin_sum
                                  (fun index : Fin 424 =>
                                    scaledCongruenceInverseEntry index.val
                                        row.val *
                                      orbitRadixRecordValue
                                        radixEncodedProductData index.val)
                            _ = ((scaledInverseDecodePairs fields).map
                                  (fun pair => pair.2 *
                                    orbitRadixRecordValue
                                      radixEncodedProductData pair.1.toNat)).sum := by
                                  rw [orbitRadixSparsePairs_weighted_sum_eq_fin
                                    fields hsorted
                                    (fun index => orbitRadixRecordValue
                                      radixEncodedProductData index)]
                                  apply Finset.sum_congr rfl
                                  intro index _
                                  rw [hlookup]
                            _ = orbitRadixSparseProductSum fields :=
                                (orbitRadixSparseProductSum_eq_pair_sum
                                  fields).symm
                            _ = congruenceInverseScale ^ 2 * encoded :=
                                hfinalRow.2
                            _ = congruenceInverseScale ^ 2 *
                                  orbitRadixReducedGramEncoding row.val := by
                                rw [htarget]

end ConnesRigidity.AffineSymplecticOrbitCertificate

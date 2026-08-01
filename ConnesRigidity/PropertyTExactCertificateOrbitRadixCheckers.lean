


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices
import ConnesRigidity.PropertyTExactCertificateOrbitBlockWeights
import ConnesRigidity.PropertyTExactCertificateOrbitRadixData
















namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section


def orbitRadixRecordValue (rows : List (List Int)) (index : Nat) : Int :=
  (rows.getD index []).getD 1 0


def orbitRadixEncodeSparsePairs : List Int → Int
  | column :: coefficient :: remaining =>
      coefficient * radixBase ^ column.toNat +
        orbitRadixEncodeSparsePairs remaining
  | _ => 0


def orbitRadixColumnSparsePairs (column : Nat) : List (Int × Int) :=
  scaledInverseDecodePairs
    ((scaledInverseColumnData.getD column []).drop 1)


def orbitRadixColumnPairLookup (column row : Nat) : Int :=
  scaledInversePairLookup (row : Int)
    ((scaledInverseColumnData.getD column []).drop 1)



def orbitRadixSparsePairsSorted : List Int → Bool
  | key :: value :: nextKey :: nextValue :: remaining =>
      decide (0 ≤ key) && decide (key < (424 : Int)) &&
        decide (value ≠ 0) && decide (key < nextKey) &&
        orbitRadixSparsePairsSorted
          (nextKey :: nextValue :: remaining)
  | [key, value] =>
      decide (0 ≤ key) && decide (key < (424 : Int)) &&
        decide (value ≠ 0)
  | [] => true
  | _ => false



def orbitRadixInverseRowPairCheck (row : Nat) : Bool :=
  match scaledInverseRowData[row]? with
  | some (storedRow :: entries) =>
      decide (storedRow = (row : Int)) &&
        orbitRadixSparsePairsSorted entries &&
        (scaledInverseDecodePairs entries).all
          (fun pair =>
            decide
              (orbitRadixColumnPairLookup pair.1.toNat row = pair.2))
  | _ => false



def orbitRadixInverseColumnPairCheck (column : Nat) : Bool :=
  match scaledInverseColumnData[column]? with
  | some (storedColumn :: entries) =>
      decide (storedColumn = (column : Int)) &&
        orbitRadixSparsePairsSorted entries &&
        (scaledInverseDecodePairs entries).all
          (fun pair =>
            decide
              (scaledCongruenceInverseEntry pair.1.toNat column = pair.2))
  | _ => false


def orbitRadixInverseRowCheck (index : Nat) : Bool :=
  match scaledInverseRowData[index]?, radixEncodedInverseData[index]? with
  | some (row :: entries), some [encodedRow, encoded] =>
      decide (row = (index : Int)) &&
        decide (encodedRow = (index : Int)) &&
        decide (orbitRadixEncodeSparsePairs entries = encoded)
  | _, _ => false


def orbitRadixBlockDotEncoded :
    List Int → List (List Int) → Int
  | coefficient :: coefficients, record :: records =>
      coefficient * record.getD 1 0 +
        orbitRadixBlockDotEncoded coefficients records
  | _, _ => 0


def orbitRadixProductRowCheck (index : Nat) : Bool :=
  match blockColumnData[index]?, radixEncodedProductData[index]? with
  | some column, some [encodedRow, encoded] =>
      let block := (column.getD 1 0).toNat
      let localIndex := (column.getD 2 0).toNat
      let coefficients := (blockGramLocalData block).getD localIndex []
      decide (column.size = 3) &&
        decide (column.getD 0 0 = (index : Int)) &&
        decide (encodedRow = (index : Int)) &&
        decide (coefficients.length = blockDimension block) &&
        decide
          (orbitRadixBlockDotEncoded coefficients
            (radixEncodedInverseData.drop (blockRowStart block)) = encoded)
  | _, _ => false



def orbitRadixSparseProductSum : List Int → Int
  | row :: coefficient :: remaining =>
      coefficient * orbitRadixRecordValue
        radixEncodedProductData row.toNat +
        orbitRadixSparseProductSum remaining
  | _ => 0


def orbitRadixFinalRowCheck (index : Nat) : Bool :=
  match scaledInverseColumnData[index]?, radixEncodedGramData[index]? with
  | some (column :: entries), some [encodedRow, encoded] =>
      decide (column = (index : Int)) &&
        decide (encodedRow = (index : Int)) &&
        decide
          (orbitRadixSparseProductSum entries =
            congruenceInverseScale ^ 2 * encoded)
  | _, _ => false


def orbitRadixReducedGramEncoding (index : Nat) : Int :=
  (List.range 424).foldr
    (fun column encoded =>
      gramEntry (index + 1) (column + 1) + radixBase * encoded)
    0





def orbitRadixDenseReducedGramEncoding (entries : List Int) : Int :=
  entries.foldr (fun coefficient encoded =>
    coefficient + radixBase * encoded) 0




def orbitRadixGramRowCheck (index : Nat) : Bool :=
  match radixDenseReducedGramRowData[index]?, radixEncodedGramData[index]? with
  | some (denseRow :: entries), some [row, encoded] =>
      decide (denseRow = (index : Int)) &&
        decide (row = (index : Int)) &&
        decide (entries.length = 424) &&
        decide (orbitRadixDenseReducedGramEncoding entries = encoded)
  | _, _ => false


def orbitRadixBlockColumnAbsSum
    (block : Nat) : List Int → Int
  | row :: coefficient :: remaining =>
      (if blockOfColumn row.toNat = block then |coefficient| else 0) +
        orbitRadixBlockColumnAbsSum block remaining
  | _ => 0


def orbitRadixBlockColumnNormCheck
    (block column : Nat) : Bool :=
  match scaledInverseColumnData[column]? with
  | some (storedColumn :: entries) =>
      decide (storedColumn = (column : Int)) &&
        decide
          (orbitRadixBlockColumnAbsSum block entries ≤
            (radixBlockBoundData.getD block []).getD 1 0)
  | _ => false


def orbitRadixBlockGramNormRowCheck
    (block localRow : Nat) : Bool :=
  let row := (blockGramLocalData block).getD localRow []
  decide (localRow < blockDimension block) &&
    decide
      (row.foldl (fun total coefficient => total + |coefficient|) 0 ≤
        (radixBlockBoundData.getD block []).getD 2 0)


def orbitRadixBlockEntryNormRowCheck (row : Nat) : Bool :=
  match scaledInverseRowData[row]? with
  | some (storedRow :: entries) =>
      let block := blockOfColumn row
      let bound := (radixBlockBoundData.getD block []).getD 3 0
      decide (storedRow = (row : Int)) &&
        (scaledInverseDecodePairs entries).all
          (fun pair => decide (|pair.2| ≤ bound))
  | _ => false



def orbitRadixBlockColumnMetadataRowCheck
    (block localRow : Nat) : Bool :=
  let globalRow := blockRowStart block + localRow
  decide (localRow < blockDimension block) &&
    decide (globalRow < 424) &&
    decide (blockOfColumn globalRow = block) &&
    decide (blockOffsetOfColumn globalRow = localRow)


def orbitRadixBlockBoundRowCheck (block : Nat) : Bool :=
  match radixBlockBoundData[block]? with
  | some [storedBlock, columnBound, gramBound, entryBound] =>
      decide (storedBlock = (block : Int)) &&
        decide (0 ≤ columnBound) &&
        decide (0 ≤ gramBound) &&
        decide (0 ≤ entryBound) &&
        (List.range 424).all (orbitRadixBlockColumnNormCheck block) &&
        (List.range (blockDimension block)).all
          (orbitRadixBlockGramNormRowCheck block) &&
        (List.range (blockDimension block)).all
          (orbitRadixBlockColumnMetadataRowCheck block) &&
        (List.range (blockDimension block)).all
          (fun localIndex =>
            orbitRadixBlockEntryNormRowCheck
              (blockRowStart block + localIndex))
  | _ => false


def orbitRadixTotalBound : Int :=
  radixBlockBoundData.foldl
    (fun total row => total +
      row.getD 1 0 * row.getD 2 0 * row.getD 3 0)
    0



def orbitRadixScaledGramBound : Int := 717551902606632157184



def orbitRadixNoCarryCheck : Bool :=
  decide (0 ≤ orbitRadixTotalBound) &&
    decide (0 ≤ orbitRadixScaledGramBound) &&
    decide (orbitRadixTotalBound + orbitRadixScaledGramBound < radixBase)


def orbitRadixGramOrbitBoundRowCheck (orbit : Nat) : Bool :=
  match gramOrbitData[orbit]? with
  | some row =>
      decide
        (|congruenceInverseScale ^ 2 * row.getD 4 0| ≤
          orbitRadixScaledGramBound)
  | _ => false


def orbitRadixRowMax (row : Nat) : Int :=
  (radixRowMaxData.getD row []).getD 1 0


def orbitRadixSparseRowMaximum : List Int → Int
  | _ :: coefficient :: remaining =>
      max |coefficient| (orbitRadixSparseRowMaximum remaining)
  | _ => 0


def orbitRadixRowMaxRowCheck (row : Nat) : Bool :=
  match scaledInverseRowData[row]?, radixRowMaxData[row]? with
  | some (storedRow :: entries), some [maximumRow, maximum] =>
      decide (storedRow = (row : Int)) &&
        decide (maximumRow = (row : Int)) &&
        decide (0 ≤ maximum) &&
        decide (orbitRadixSparseRowMaximum entries = maximum)
  | _, _ => false



def orbitRadixWeightedGramRow
    (block offset : Nat) : List Int → Int
  | coefficient :: remaining =>
      |coefficient| * orbitRadixRowMax (blockRowStart block + offset) +
        orbitRadixWeightedGramRow block (offset + 1) remaining
  | [] => 0


def orbitRadixComputedBlockRowMaxBound (block : Nat) : Int :=
  (List.range (blockDimension block)).foldl
    (fun total row =>
      total + orbitRadixRowMax (blockRowStart block + row) *
        orbitRadixWeightedGramRow block 0
          ((blockGramLocalData block).getD row []))
    0


def orbitRadixBlockRowMaxBoundCheck (block : Nat) : Bool :=
  match radixBlockRowMaxBoundData[block]? with
  | some [storedBlock, bound] =>
      decide (storedBlock = (block : Int)) &&
        decide (0 ≤ bound) &&
        (blockGramLocalData block).all
          (fun row => decide (row.length = blockDimension block)) &&
        decide (orbitRadixComputedBlockRowMaxBound block = bound)
  | _ => false


def orbitRadixRowMaxTotalBound : Int :=
  radixBlockRowMaxBoundData.foldl
    (fun total row => total + row.getD 1 0) 0



def orbitRadixRowMaxTotalNoCarryCheck : Bool :=
  decide (0 ≤ orbitRadixRowMaxTotalBound) &&
    decide
      (orbitRadixRowMaxTotalBound + orbitRadixScaledGramBound < radixBase)


def orbitRadixRowMaxCheck : Bool :=
  (List.range 424).all orbitRadixRowMaxRowCheck


def orbitRadixBlockRowMaxBoundGlobalCheck : Bool :=
  (List.range 28).all orbitRadixBlockRowMaxBoundCheck


def orbitRadixInverseCheck : Bool :=
  (List.range 424).all orbitRadixInverseRowCheck


def orbitRadixInverseTransposeCheck : Bool :=
  (List.range 424).all orbitRadixInverseRowPairCheck &&
    (List.range 424).all orbitRadixInverseColumnPairCheck


def orbitRadixProductCheck : Bool :=
  (List.range 424).all orbitRadixProductRowCheck


def orbitRadixFinalCheck : Bool :=
  (List.range 424).all orbitRadixFinalRowCheck


def orbitRadixGramCheck : Bool :=
  (List.range 424).all orbitRadixGramRowCheck


def orbitRadixBlockBoundCheck : Bool :=
  (List.range blockCount).all orbitRadixBlockBoundRowCheck


def orbitRadixGramOrbitBoundCheck : Bool :=
  (List.range gramOrbitData.size).all orbitRadixGramOrbitBoundRowCheck



def orbitRadixGramOrbitBoundStreamingCheck : Bool :=
  gramOrbitData.toList.all
    (fun row =>
      decide
        (|congruenceInverseScale ^ 2 * row.getD 4 0| ≤
          orbitRadixScaledGramBound))

theorem orbitRadixInverseRowCheck_sound
    (index : Nat) (row encoded : Int) (entries : List Int)
    (hrow : scaledInverseRowData[index]? = some (row :: entries))
    (hencoded : radixEncodedInverseData[index]? = some [row, encoded])
    (hcheck : orbitRadixInverseRowCheck index = true) :
    row = (index : Int) ∧
      orbitRadixEncodeSparsePairs entries = encoded := by
  simp only [orbitRadixInverseRowCheck, hrow, hencoded,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1, hcheck.2⟩

theorem orbitRadixInverseRowPairCheck_sound
    (index : Nat) (row : Int) (entries : List Int)
    (hrow : scaledInverseRowData[index]? = some (row :: entries))
    (hcheck : orbitRadixInverseRowPairCheck index = true) :
    row = (index : Int) ∧
      orbitRadixSparsePairsSorted entries = true ∧
      (scaledInverseDecodePairs entries).all
        (fun pair =>
          decide
            (orbitRadixColumnPairLookup pair.1.toNat index = pair.2)) =
        true := by
  simp only [orbitRadixInverseRowPairCheck, hrow,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2, hcheck.2⟩

theorem orbitRadixInverseColumnPairCheck_sound
    (index : Nat) (column : Int) (entries : List Int)
    (hcolumn : scaledInverseColumnData[index]? =
      some (column :: entries))
    (hcheck : orbitRadixInverseColumnPairCheck index = true) :
    column = (index : Int) ∧
      orbitRadixSparsePairsSorted entries = true ∧
      (scaledInverseDecodePairs entries).all
        (fun pair =>
          decide
            (scaledCongruenceInverseEntry pair.1.toNat index = pair.2)) =
        true := by
  simp only [orbitRadixInverseColumnPairCheck, hcolumn,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2, hcheck.2⟩

theorem orbitRadixProductRowCheck_sound
    (index : Nat) (column : Array Int) (row encoded : Int)
    (hcolumn : blockColumnData[index]? = some column)
    (hencoded : radixEncodedProductData[index]? = some [row, encoded])
    (hcheck : orbitRadixProductRowCheck index = true) :
    column.size = 3 ∧
      column.getD 0 0 = (index : Int) ∧
      row = (index : Int) ∧
      ((blockGramLocalData (column.getD 1 0).toNat).getD
        (column.getD 2 0).toNat []).length =
          blockDimension (column.getD 1 0).toNat ∧
      orbitRadixBlockDotEncoded
        ((blockGramLocalData (column.getD 1 0).toNat).getD
          (column.getD 2 0).toNat [])
        (radixEncodedInverseData.drop
          (blockRowStart (column.getD 1 0).toNat)) = encoded := by
  simp only [orbitRadixProductRowCheck, hcolumn, hencoded,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hwidth, hindex⟩, hrow⟩, hlength⟩, hdot⟩
  exact ⟨hwidth, hindex, hrow, hlength, hdot⟩

theorem orbitRadixFinalRowCheck_sound
    (index : Nat) (column encoded : Int) (entries : List Int)
    (hcolumn : scaledInverseColumnData[index]? =
      some (column :: entries))
    (hencoded : radixEncodedGramData[index]? = some [column, encoded])
    (hcheck : orbitRadixFinalRowCheck index = true) :
    column = (index : Int) ∧
      orbitRadixSparseProductSum entries =
        congruenceInverseScale ^ 2 * encoded := by
  simp only [orbitRadixFinalRowCheck, hcolumn, hencoded,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1, hcheck.2⟩

theorem orbitRadixGramRowCheck_sound
    (index : Nat) (denseRow row encoded : Int) (entries : List Int)
    (hdense : radixDenseReducedGramRowData[index]? =
      some (denseRow :: entries))
    (hrow : radixEncodedGramData[index]? = some [row, encoded])
    (hcheck : orbitRadixGramRowCheck index = true) :
    denseRow = (index : Int) ∧
      row = (index : Int) ∧
      entries.length = 424 ∧
      orbitRadixDenseReducedGramEncoding entries = encoded := by
  simp only [orbitRadixGramRowCheck, hdense, hrow,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1.1, hcheck.1.1.2, hcheck.1.2, hcheck.2⟩

theorem orbitRadixBlockColumnNormCheck_sound
    (block column : Nat) (storedColumn : Int) (entries : List Int)
    (hcolumn : scaledInverseColumnData[column]? =
      some (storedColumn :: entries))
    (hcheck : orbitRadixBlockColumnNormCheck block column = true) :
    storedColumn = (column : Int) ∧
      orbitRadixBlockColumnAbsSum block entries ≤
        (radixBlockBoundData.getD block []).getD 1 0 := by
  simpa only [orbitRadixBlockColumnNormCheck, hcolumn,
    Bool.and_eq_true, decide_eq_true_eq] using hcheck

theorem orbitRadixBlockGramNormRowCheck_sound
    (block row : Nat)
    (hcheck : orbitRadixBlockGramNormRowCheck block row = true) :
    row < blockDimension block ∧
      ((blockGramLocalData block).getD row []).foldl
        (fun total coefficient => total + |coefficient|) 0 ≤
          (radixBlockBoundData.getD block []).getD 2 0 := by
  simpa only [orbitRadixBlockGramNormRowCheck,
    Bool.and_eq_true, decide_eq_true_eq] using hcheck

theorem orbitRadixBlockEntryNormRowCheck_sound
    (index : Nat) (row : Int) (entries : List Int)
    (hrow : scaledInverseRowData[index]? = some (row :: entries))
    (hcheck : orbitRadixBlockEntryNormRowCheck index = true) :
    row = (index : Int) ∧
      (scaledInverseDecodePairs entries).all
        (fun pair =>
          decide
            (|pair.2| ≤
              (radixBlockBoundData.getD (blockOfColumn index) []).getD
                3 0)) = true := by
  simpa only [orbitRadixBlockEntryNormRowCheck, hrow,
    Bool.and_eq_true, decide_eq_true_eq] using hcheck

theorem orbitRadixBlockBoundRowCheck_sound
    (block : Nat) (storedBlock columnBound gramBound entryBound : Int)
    (hrow : radixBlockBoundData[block]? =
      some [storedBlock, columnBound, gramBound, entryBound])
    (hcheck : orbitRadixBlockBoundRowCheck block = true) :
    storedBlock = (block : Int) ∧
      0 ≤ columnBound ∧ 0 ≤ gramBound ∧ 0 ≤ entryBound ∧
      (List.range 424).all (orbitRadixBlockColumnNormCheck block) = true ∧
      (List.range (blockDimension block)).all
        (orbitRadixBlockGramNormRowCheck block) = true ∧
      (List.range (blockDimension block)).all
        (orbitRadixBlockColumnMetadataRowCheck block) = true ∧
      (List.range (blockDimension block)).all
        (fun row =>
          orbitRadixBlockEntryNormRowCheck (blockRowStart block + row)) =
        true := by
  simp only [orbitRadixBlockBoundRowCheck, hrow,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨⟨hblock, hcolumn⟩, hgram⟩, hentry⟩,
      hcolumns⟩, hrows⟩, hmetadata⟩, hentries⟩
  exact ⟨hblock, hcolumn, hgram, hentry,
    hcolumns, hrows, hmetadata, hentries⟩

theorem orbitRadixBlockColumnMetadataRowCheck_sound
    (block row : Nat)
    (hcheck : orbitRadixBlockColumnMetadataRowCheck block row = true) :
    row < blockDimension block ∧
      blockRowStart block + row < 424 ∧
      blockOfColumn (blockRowStart block + row) = block ∧
      blockOffsetOfColumn (blockRowStart block + row) = row := by
  simp only [orbitRadixBlockColumnMetadataRowCheck,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hrange, hglobal⟩, hblock⟩, hoffset⟩
  exact ⟨hrange, hglobal, hblock, hoffset⟩

theorem orbitRadixGramOrbitBoundRowCheck_sound
    (orbit : Nat) (row : Array Int)
    (hrow : gramOrbitData[orbit]? = some row)
    (hcheck : orbitRadixGramOrbitBoundRowCheck orbit = true) :
    |congruenceInverseScale ^ 2 * row.getD 4 0| ≤
      orbitRadixScaledGramBound := by
  simpa only [orbitRadixGramOrbitBoundRowCheck, hrow,
    decide_eq_true_eq] using hcheck

theorem orbitRadixGramOrbitBoundStreamingCheck_sound
    (hcheck : orbitRadixGramOrbitBoundStreamingCheck = true)
    (orbit : Nat) (row : Array Int)
    (hrow : gramOrbitData[orbit]? = some row) :
    |congruenceInverseScale ^ 2 * row.getD 4 0| ≤
      orbitRadixScaledGramBound := by
  have hmember : row ∈ gramOrbitData.toList := by
    exact Array.mem_toList_iff.mpr
      (Array.mem_iff_getElem?.mpr ⟨orbit, hrow⟩)
  have hrowCheck :=
    (List.all_eq_true.mp hcheck) row hmember
  simpa only [orbitRadixGramOrbitBoundStreamingCheck,
    decide_eq_true_eq] using hrowCheck

theorem orbitRadixRowMaxRowCheck_sound
    (index : Nat) (row maximumRow maximum : Int) (entries : List Int)
    (hrow : scaledInverseRowData[index]? = some (row :: entries))
    (hmaximum : radixRowMaxData[index]? =
      some [maximumRow, maximum])
    (hcheck : orbitRadixRowMaxRowCheck index = true) :
    row = (index : Int) ∧
      maximumRow = (index : Int) ∧
      0 ≤ maximum ∧
      orbitRadixSparseRowMaximum entries = maximum := by
  simp only [orbitRadixRowMaxRowCheck, hrow, hmaximum,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hrow, hmaximum⟩, hpositive⟩, hvalue⟩
  exact ⟨hrow, hmaximum, hpositive, hvalue⟩



theorem orbitRadixSparseLookup_abs_le_max (column : Int) :
    (entries : List Int) →
      |scaledInversePairLookup column entries| ≤
        orbitRadixSparseRowMaximum entries
  | [] => by
      simp [scaledInversePairLookup, orbitRadixSparseRowMaximum]
  | [_] => by
      simp [scaledInversePairLookup, orbitRadixSparseRowMaximum]
  | key :: value :: remaining => by
      by_cases hkey : key = column
      · simp [scaledInversePairLookup, orbitRadixSparseRowMaximum,
          hkey]
      · simp only [scaledInversePairLookup, hkey, ↓reduceIte,
          orbitRadixSparseRowMaximum]
        exact le_trans
          (orbitRadixSparseLookup_abs_le_max column remaining)
          (le_max_right _ _)



theorem orbitRadixRowMaxRowCheck_bound
    (row column : Nat)
    (hcheck : orbitRadixRowMaxRowCheck row = true) :
    0 ≤ orbitRadixRowMax row ∧
      |scaledCongruenceInverseEntry row column| ≤
        orbitRadixRowMax row := by
  have hchecked := hcheck
  unfold orbitRadixRowMaxRowCheck at hcheck
  generalize hsource : scaledInverseRowData[row]? = source at hcheck
  generalize hmaximum : radixRowMaxData[row]? = maximum at hcheck
  cases source with
  | none => contradiction
  | some source =>
    cases source with
    | nil => contradiction
    | cons storedRow entries =>
      cases maximum with
      | none => contradiction
      | some maximum =>
        cases maximum with
        | nil => contradiction
        | cons maximumRow tail =>
          cases tail with
          | nil => contradiction
          | cons maximumValue remaining =>
            cases remaining with
            | cons _ _ => contradiction
            | nil =>
              have hproperties := orbitRadixRowMaxRowCheck_sound
                row storedRow maximumRow maximumValue entries
                  hsource hmaximum hchecked
              have hmax : orbitRadixRowMax row = maximumValue := by
                unfold orbitRadixRowMax
                change ((radixRowMaxData[row]?).getD []).getD 1 0 = _
                rw [hmaximum]
                rfl
              have hentry :
                  scaledCongruenceInverseEntry row column =
                    scaledInversePairLookup (column : Int) entries := by
                unfold scaledCongruenceInverseEntry
                change
                  scaledInversePairLookup (column : Int)
                    (((scaledInverseRowData[row]?).getD []).drop 1) = _
                rw [hsource]
                rfl
              refine ⟨hmax.symm ▸ hproperties.2.2.1, ?_⟩
              rw [hentry, hmax, ← hproperties.2.2.2]
              exact orbitRadixSparseLookup_abs_le_max (column : Int) entries

theorem orbitRadixBlockRowMaxBoundCheck_sound
    (block : Nat) (storedBlock bound : Int)
    (hrow : radixBlockRowMaxBoundData[block]? =
      some [storedBlock, bound])
    (hcheck : orbitRadixBlockRowMaxBoundCheck block = true) :
    storedBlock = (block : Int) ∧
      0 ≤ bound ∧
      (blockGramLocalData block).all
        (fun row => decide (row.length = blockDimension block)) = true ∧
      orbitRadixComputedBlockRowMaxBound block = bound := by
  simp only [orbitRadixBlockRowMaxBoundCheck, hrow,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1.1, hcheck.1.1.2, hcheck.1.2, hcheck.2⟩

theorem orbitRadixRowMaxTotalNoCarryCheck_sound
    (hcheck : orbitRadixRowMaxTotalNoCarryCheck = true) :
    0 ≤ orbitRadixRowMaxTotalBound ∧
      orbitRadixRowMaxTotalBound + orbitRadixScaledGramBound < radixBase := by
  simpa only [orbitRadixRowMaxTotalNoCarryCheck,
    Bool.and_eq_true, decide_eq_true_eq] using hcheck

theorem orbitRadixNoCarryCheck_sound
    (hcheck : orbitRadixNoCarryCheck = true) :
    0 ≤ orbitRadixTotalBound ∧
      0 ≤ orbitRadixScaledGramBound ∧
      orbitRadixTotalBound + orbitRadixScaledGramBound < radixBase := by
  simp only [orbitRadixNoCarryCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2, hcheck.2⟩

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

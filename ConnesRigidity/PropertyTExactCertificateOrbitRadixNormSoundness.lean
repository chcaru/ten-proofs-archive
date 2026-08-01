
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices
import ConnesRigidity.PropertyTExactCertificateOrbitBlockWeights
import ConnesRigidity.PropertyTExactCertificateOrbitRadixData
import ConnesRigidity.PropertyTExactCertificateOrbitRadixCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitRadixValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

set_option maxRecDepth 1000000

noncomputable def orbitRadixColumnBound (block : Nat) : Int :=
  (radixBlockBoundData.getD block []).getD 1 0

noncomputable def orbitRadixBlockRowBound (block : Nat) : Int :=
  (radixBlockBoundData.getD block []).getD 2 0

noncomputable def orbitRadixEntryBound (block : Nat) : Int :=
  (radixBlockBoundData.getD block []).getD 3 0

noncomputable def orbitRadixRowMaximum (row : Nat) : Int :=
  (radixRowMaxData.getD row []).getD 1 0

noncomputable def orbitRadixBlockRowMaximumBound (block : Nat) : Int :=
  (radixBlockRowMaxBoundData.getD block []).getD 1 0

noncomputable def orbitRadixBlockComputedEntry
    (block : Nat) (row column : Fin 424) : Int :=
  ∑ offset : Fin (blockDimension block),
    scaledCongruenceInverseEntry
      (blockRowStart block + offset.val) row.val *
      ∑ other : Fin (blockDimension block),
        blockGramEntryInt block offset.val other.val *
          scaledCongruenceInverseEntry
            (blockRowStart block + other.val) column.val

noncomputable def orbitRadixComputedEntry
    (row column : Fin 424) : Int :=
  ∑ block : Fin 28,
    orbitRadixBlockComputedEntry block.val row column

noncomputable def orbitRadixBlockRowMaximumExpression (block : Nat) : Int :=
  ∑ row : Fin (blockDimension block),
    orbitRadixRowMaximum (blockRowStart block + row.val) *
      ∑ column : Fin (blockDimension block),
        |blockGramEntryInt block row.val column.val| *
          orbitRadixRowMaximum (blockRowStart block + column.val)

theorem scaledInversePairLookup_abs_le_of_all
    (column bound : Int) (fields : List Int)
    (hbound : 0 ≤ bound)
    (hentries : (scaledInverseDecodePairs fields).all
      (fun pair => decide (|pair.2| ≤ bound)) = true) :
    |scaledInversePairLookup column fields| ≤ bound := by
  induction fields using scaledInversePairLookup.induct column with
  | case1 value remaining =>
      simp only [scaledInverseDecodePairs, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hentries
      simpa [scaledInversePairLookup] using hentries.1
  | case2 key value remaining hne ih =>
      simp only [scaledInverseDecodePairs, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hentries
      simpa [scaledInversePairLookup, hne] using ih hentries.2
  | case3 fields hshort =>
      cases fields with
      | nil => simpa [scaledInversePairLookup] using hbound
      | cons first remaining =>
          cases remaining with
          | nil => simpa [scaledInversePairLookup] using hbound
          | cons second tail =>
              exact False.elim (hshort first second tail rfl)

theorem orbitRadix_block_abs_le_row_max
    {α : Type*} [Fintype α]
    (left right : α → Int) (gram : α → α → Int)
    (rowMaximum : α → Int)
    (hleft : ∀ index, |left index| ≤ rowMaximum index)
    (hright : ∀ index, |right index| ≤ rowMaximum index)
    (hmaximum : ∀ index, 0 ≤ rowMaximum index) :
    |∑ index, left index * ∑ other, gram index other * right other| ≤
      ∑ index, rowMaximum index *
        ∑ other, |gram index other| * rowMaximum other := by
  have hinner (index : α) :
      |∑ other, gram index other * right other| ≤
        ∑ other, |gram index other| * rowMaximum other := by
    calc
      |∑ other, gram index other * right other| ≤
          ∑ other, |gram index other * right other| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ other, |gram index other| * |right other| := by
        simp_rw [abs_mul]
      _ ≤ ∑ other, |gram index other| * rowMaximum other := by
        exact Finset.sum_le_sum fun other _ =>
          mul_le_mul_of_nonneg_left (hright other) (abs_nonneg _)
  calc
    |∑ index, left index * ∑ other, gram index other * right other| ≤
        ∑ index, |left index * ∑ other, gram index other * right other| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ index, |left index| *
        |∑ other, gram index other * right other| := by
      simp_rw [abs_mul]
    _ ≤ ∑ index, rowMaximum index *
        ∑ other, |gram index other| * rowMaximum other := by
      apply Finset.sum_le_sum
      intro index _
      exact mul_le_mul (hleft index) (hinner index)
        (abs_nonneg _)
        (hmaximum index)

theorem orbitRadixBlockComputedEntry_abs_le_row_max
    (block : Nat) (row column : Fin 424)
    (hmaximum : ∀ offset : Fin (blockDimension block),
      0 ≤ orbitRadixRowMaximum (blockRowStart block + offset.val))
    (hleft : ∀ offset : Fin (blockDimension block),
      |scaledCongruenceInverseEntry
        (blockRowStart block + offset.val) row.val| ≤
          orbitRadixRowMaximum (blockRowStart block + offset.val))
    (hright : ∀ offset : Fin (blockDimension block),
      |scaledCongruenceInverseEntry
        (blockRowStart block + offset.val) column.val| ≤
          orbitRadixRowMaximum (blockRowStart block + offset.val)) :
    |orbitRadixBlockComputedEntry block row column| ≤
      orbitRadixBlockRowMaximumExpression block := by
  unfold orbitRadixBlockComputedEntry orbitRadixBlockRowMaximumExpression
  exact orbitRadix_block_abs_le_row_max
    (fun offset : Fin (blockDimension block) =>
      scaledCongruenceInverseEntry
        (blockRowStart block + offset.val) row.val)
    (fun offset : Fin (blockDimension block) =>
      scaledCongruenceInverseEntry
        (blockRowStart block + offset.val) column.val)
    (fun left right : Fin (blockDimension block) =>
      blockGramEntryInt block left.val right.val)
    (fun offset : Fin (blockDimension block) =>
      orbitRadixRowMaximum (blockRowStart block + offset.val))
    hleft hright hmaximum

theorem orbitRadixWeightedGramRow_eq_fin_sum
    (block offset : Nat) (entries : List Int) :
    orbitRadixWeightedGramRow block offset entries =
      ∑ index : Fin entries.length,
        |entries.getD index.val 0| *
          orbitRadixRowMax (blockRowStart block + offset + index.val) := by
  induction entries generalizing offset with
  | nil => simp [orbitRadixWeightedGramRow]
  | cons entry entries ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [orbitRadixWeightedGramRow, Fin.val_zero,
        List.getD_cons_zero, Nat.add_zero,
        Fin.val_succ, List.getD_cons_succ]
      rw [ih (offset + 1)]
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      congr 2
      omega

private theorem orbitRadix_foldl_range_eq_fin_sum
    (value : Nat → Int) (count : Nat) :
    (List.range count).foldl
      (fun total index => total + value index) 0 =
      ∑ index : Fin count, value index.val := by
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      rw [Fin.sum_univ_eq_sum_range]
      simp only [Finset.sum_range_succ]
      rw [← Fin.sum_univ_eq_sum_range]
      exact congrArg (fun total => total + value count) ih

theorem orbitRadixComputedBlockRowMaxBound_eq_expression
    (block : Nat)
    (hwidth : ∀ row : Fin (blockDimension block),
      ((blockGramLocalData block).getD row.val []).length =
        blockDimension block) :
    orbitRadixComputedBlockRowMaxBound block =
      orbitRadixBlockRowMaximumExpression block := by
  unfold orbitRadixComputedBlockRowMaxBound
    orbitRadixBlockRowMaximumExpression
  rw [orbitRadix_foldl_range_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro row _
  congr 1
  rw [orbitRadixWeightedGramRow_eq_fin_sum,
    hwidth row]
  apply Finset.sum_congr rfl
  intro column _
  simp only [blockGramEntryInt, orbitRadixRowMaximum,
    orbitRadixRowMax, Nat.add_zero]

theorem orbitRadixBlock_coordinate_range (block : Fin 28) :
    blockRowStart block.val + blockDimension block.val ≤ 424 := by
  fin_cases block <;> decide +kernel

theorem orbitRadixBlock_gram_row_count (block : Fin 28) :
    (blockGramLocalData block.val).length = blockDimension block.val := by
  fin_cases block <;> decide +kernel

private theorem orbitRadix_foldl_rows_eq_fin_sum
    (rows : List (List Int)) :
    rows.foldl (fun total row => total + row.getD 1 0) 0 =
      ∑ row : Fin rows.length, (rows.getD row.val []).getD 1 0 := by
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simpa using congrArg (fun value => row.getD 1 0 + value) ih

theorem orbitRadixRowMaxTotalBound_eq_fin_sum :
    orbitRadixRowMaxTotalBound =
      ∑ block : Fin 28, orbitRadixBlockRowMaximumBound block.val := by
  unfold orbitRadixRowMaxTotalBound orbitRadixBlockRowMaximumBound
  rw [orbitRadix_foldl_rows_eq_fin_sum]
  have hlength : radixBlockRowMaxBoundData.length = 28 := by
    decide +kernel
  rw [hlength]

theorem orbitRadixBlockRowMaxBoundCheck_properties
    (block : Fin 28)
    (hcheck : orbitRadixBlockRowMaxBoundCheck block.val = true) :
    (∀ row : Fin (blockDimension block.val),
      ((blockGramLocalData block.val).getD row.val []).length =
        blockDimension block.val) ∧
      orbitRadixComputedBlockRowMaxBound block.val =
        orbitRadixBlockRowMaximumBound block.val := by
  generalize hrecord : radixBlockRowMaxBoundData[block.val]? = record
  cases record with
  | none =>
      simp [orbitRadixBlockRowMaxBoundCheck, hrecord] at hcheck
  | some record =>
      cases record with
      | nil =>
          simp [orbitRadixBlockRowMaxBoundCheck, hrecord] at hcheck
      | cons stored rest =>
          cases rest with
          | nil =>
              simp [orbitRadixBlockRowMaxBoundCheck, hrecord] at hcheck
          | cons bound remaining =>
              cases remaining with
              | cons _ _ =>
                  simp [orbitRadixBlockRowMaxBoundCheck, hrecord] at hcheck
              | nil =>
                  have hproperties := orbitRadixBlockRowMaxBoundCheck_sound
                    block.val stored bound hrecord hcheck
                  have hbound :
                      orbitRadixBlockRowMaximumBound block.val = bound := by
                    unfold orbitRadixBlockRowMaximumBound
                    change
                      ((radixBlockRowMaxBoundData[block.val]?).getD []).getD
                        1 0 = bound
                    rw [hrecord]
                    rfl
                  constructor
                  · intro row
                    have hindex :
                        row.val < (blockGramLocalData block.val).length := by
                      rw [orbitRadixBlock_gram_row_count block]
                      exact row.isLt
                    have hmember :
                        (blockGramLocalData block.val).getD row.val [] ∈
                          blockGramLocalData block.val := by
                      rw [List.getD_eq_getElem?_getD,
                        List.getElem?_eq_getElem hindex]
                      simp
                    simpa only [decide_eq_true_eq] using
                      (List.all_eq_true.mp hproperties.2.2.1) _ hmember
                  · simpa [hbound] using hproperties.2.2.2

theorem orbitRadix_scaledGramEntry_abs_le_of_check
    (hcheck : orbitRadixGramOrbitBoundStreamingCheck = true)
    (left right : Nat) :
    |congruenceInverseScale ^ 2 * gramEntry left right| ≤
      orbitRadixScaledGramBound := by
  change
    |congruenceInverseScale ^ 2 *
      (gramOrbitData.getD (pairOrbit left right) #[]).getD 4 0| ≤
        orbitRadixScaledGramBound
  generalize horbit : pairOrbit left right = orbit
  rw [Array.getD_eq_getD_getElem?]
  cases hrow : gramOrbitData[orbit]? with
  | none =>
      simp [hrow, orbitRadixScaledGramBound]
  | some row =>
      simpa [hrow] using
        orbitRadixGramOrbitBoundStreamingCheck_sound hcheck orbit row hrow

theorem orbitRadix_block_abs_le
    {α : Type*} [Fintype α]
    (left right : α → Int) (gram : α → α → Int)
    (columnBound rowBound entryBound : Int)
    (hcolumn : ∑ index, |left index| ≤ columnBound)
    (hrow : ∀ index, ∑ other, |gram index other| ≤ rowBound)
    (hentry : ∀ index, |right index| ≤ entryBound)
    (hrow_nonneg : 0 ≤ rowBound)
    (hentry_nonneg : 0 ≤ entryBound) :
    |∑ index, left index * ∑ other, gram index other * right other| ≤
      columnBound * rowBound * entryBound := by
  have hinner (index : α) :
      |∑ other, gram index other * right other| ≤
        rowBound * entryBound := by
    calc
      |∑ other, gram index other * right other| ≤
          ∑ other, |gram index other * right other| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ other, |gram index other| * |right other| := by
        simp_rw [abs_mul]
      _ ≤ ∑ other, |gram index other| * entryBound := by
        exact Finset.sum_le_sum fun other _ =>
          mul_le_mul_of_nonneg_left (hentry other) (abs_nonneg _)
      _ = (∑ other, |gram index other|) * entryBound := by
        rw [Finset.sum_mul]
      _ ≤ rowBound * entryBound :=
        mul_le_mul_of_nonneg_right (hrow index) hentry_nonneg
  calc
    |∑ index, left index * ∑ other, gram index other * right other| ≤
        ∑ index, |left index * ∑ other, gram index other * right other| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ index, |left index| * |∑ other, gram index other * right other| := by
      simp_rw [abs_mul]
    _ ≤ ∑ index, |left index| * (rowBound * entryBound) := by
      exact Finset.sum_le_sum fun index _ =>
        mul_le_mul_of_nonneg_left (hinner index) (abs_nonneg _)
    _ = (∑ index, |left index|) * (rowBound * entryBound) := by
      rw [Finset.sum_mul]
    _ ≤ columnBound * (rowBound * entryBound) := by
      exact mul_le_mul_of_nonneg_right hcolumn
        (mul_nonneg hrow_nonneg hentry_nonneg)
    _ = columnBound * rowBound * entryBound := by ring

theorem orbitRadixBlockComputedEntry_abs_le
    (block : Nat) (row column : Fin 424)
    (hcolumn :
      (∑ offset : Fin (blockDimension block),
        |scaledCongruenceInverseEntry
          (blockRowStart block + offset.val) row.val|) ≤
        orbitRadixColumnBound block)
    (hrow : ∀ offset : Fin (blockDimension block),
      (∑ other : Fin (blockDimension block),
        |blockGramEntryInt block offset.val other.val|) ≤
          orbitRadixBlockRowBound block)
    (hentry : ∀ offset : Fin (blockDimension block),
      |scaledCongruenceInverseEntry
        (blockRowStart block + offset.val) column.val| ≤
          orbitRadixEntryBound block)
    (hrow_nonneg : 0 ≤ orbitRadixBlockRowBound block)
    (hentry_nonneg : 0 ≤ orbitRadixEntryBound block) :
    |orbitRadixBlockComputedEntry block row column| ≤
      orbitRadixColumnBound block *
        orbitRadixBlockRowBound block * orbitRadixEntryBound block := by
  unfold orbitRadixBlockComputedEntry
  exact orbitRadix_block_abs_le
    (fun offset : Fin (blockDimension block) =>
      scaledCongruenceInverseEntry
        (blockRowStart block + offset.val) row.val)
    (fun offset : Fin (blockDimension block) =>
      scaledCongruenceInverseEntry
        (blockRowStart block + offset.val) column.val)
    (fun offset other : Fin (blockDimension block) =>
      blockGramEntryInt block offset.val other.val)
    (orbitRadixColumnBound block)
    (orbitRadixBlockRowBound block)
    (orbitRadixEntryBound block)
    hcolumn hrow hentry hrow_nonneg hentry_nonneg

theorem orbitRadixComputedEntry_abs_le
    (row column : Fin 424)
    (hblocks : ∀ block : Fin 28,
      |orbitRadixBlockComputedEntry block.val row column| ≤
        orbitRadixColumnBound block.val *
          orbitRadixBlockRowBound block.val *
          orbitRadixEntryBound block.val) :
    |orbitRadixComputedEntry row column| ≤
      ∑ block : Fin 28,
        orbitRadixColumnBound block.val *
          orbitRadixBlockRowBound block.val *
          orbitRadixEntryBound block.val := by
  unfold orbitRadixComputedEntry
  exact le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum fun block _ => hblocks block)

theorem orbitRadix_matrix_difference_bound_of_bounds
    (row column : Fin 424)
    (computedBound targetBound : Int)
    (hcomputed : |orbitRadixComputedEntry row column| ≤ computedBound)
    (htarget :
      |congruenceInverseScale ^ 2 *
        gramEntry (row.val + 1) (column.val + 1)| ≤ targetBound)
    (hnocarry : computedBound + targetBound < radixBase) :
    -radixBase <
        orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) ∧
      orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) < radixBase := by
  apply abs_lt.mp
  calc
    |orbitRadixComputedEntry row column -
        congruenceInverseScale ^ 2 *
          gramEntry (row.val + 1) (column.val + 1)| ≤
        |orbitRadixComputedEntry row column| +
          |congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (orbitRadixComputedEntry row column)
          (-(congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1)))
    _ ≤ computedBound + targetBound := add_le_add hcomputed htarget
    _ < radixBase := hnocarry

theorem orbitRadix_matrix_difference_bound_of_checks
    (hrows : ∀ index : Fin 424,
      orbitRadixRowMaxRowCheck index.val = true)
    (hblocks : ∀ block : Fin 28,
      orbitRadixBlockRowMaxBoundCheck block.val = true)
    (hgram : orbitRadixGramOrbitBoundStreamingCheck = true)
    (hnocarry : orbitRadixRowMaxTotalNoCarryCheck = true)
    (row column : Fin 424) :
    -radixBase <
        orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) ∧
      orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) < radixBase := by
  apply orbitRadix_matrix_difference_bound_of_bounds row column
    orbitRadixRowMaxTotalBound orbitRadixScaledGramBound
  · have hblock (block : Fin 28) :
        |orbitRadixBlockComputedEntry block.val row column| ≤
          orbitRadixBlockRowMaximumBound block.val := by
      obtain ⟨hwidth, hbound⟩ :=
        orbitRadixBlockRowMaxBoundCheck_properties block (hblocks block)
      have hindex (offset : Fin (blockDimension block.val)) :
          blockRowStart block.val + offset.val < 424 := by
        have hrange := orbitRadixBlock_coordinate_range block
        omega
      have hrowBound (offset : Fin (blockDimension block.val))
          (index : Nat) :
          0 ≤ orbitRadixRowMaximum
              (blockRowStart block.val + offset.val) ∧
            |scaledCongruenceInverseEntry
              (blockRowStart block.val + offset.val) index| ≤
                orbitRadixRowMaximum
                  (blockRowStart block.val + offset.val) := by
        simpa only [orbitRadixRowMaximum, orbitRadixRowMax] using
          orbitRadixRowMaxRowCheck_bound
            (blockRowStart block.val + offset.val) index
            (hrows ⟨blockRowStart block.val + offset.val,
              hindex offset⟩)
      calc
        |orbitRadixBlockComputedEntry block.val row column| ≤
            orbitRadixBlockRowMaximumExpression block.val :=
          orbitRadixBlockComputedEntry_abs_le_row_max block.val row column
            (fun offset => (hrowBound offset row.val).1)
            (fun offset => (hrowBound offset row.val).2)
            (fun offset => (hrowBound offset column.val).2)
        _ = orbitRadixComputedBlockRowMaxBound block.val :=
          (orbitRadixComputedBlockRowMaxBound_eq_expression
            block.val hwidth).symm
        _ = orbitRadixBlockRowMaximumBound block.val := hbound
    calc
      |orbitRadixComputedEntry row column| ≤
          ∑ block : Fin 28,
            |orbitRadixBlockComputedEntry block.val row column| := by
        unfold orbitRadixComputedEntry
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ block : Fin 28,
          orbitRadixBlockRowMaximumBound block.val :=
        Finset.sum_le_sum fun block _ => hblock block
      _ = orbitRadixRowMaxTotalBound :=
        orbitRadixRowMaxTotalBound_eq_fin_sum.symm
  · exact orbitRadix_scaledGramEntry_abs_le_of_check hgram
      (row.val + 1) (column.val + 1)
  · exact (orbitRadixRowMaxTotalNoCarryCheck_sound hnocarry).2

theorem orbitRadix_matrix_difference_bound
    (row column : Fin 424) :
    -radixBase <
        orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) ∧
      orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) < radixBase :=
  orbitRadix_matrix_difference_bound_of_checks
    orbitRadixRowMaxRowCheck_valid
    orbitRadixBlockRowMaxBoundCheck_valid
    orbitRadixGramOrbitBoundStreamingCheck_valid
    orbitRadixRowMaxTotalNoCarryCheck_valid row column

end ConnesRigidity.AffineSymplecticOrbitCertificate


import ConnesRigidity.PropertyTExactCertificateCoefficientChecks
import ConnesRigidity.PropertyTExactCertificateCoefficientSourceSoundness
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

private def coefficientEncodingBase : Int :=
  18446744073709551616

private def encodeCoefficientRow (entries : List Int) : Int :=
  entries.foldr
    (fun entry result => entry + coefficientEncodingBase * result) 0

private theorem encodeCoefficientRow_injective_of_difference_bound
    {left right : List Int}
    (bounds : List.Forall₂
      (fun x y =>
        -coefficientEncodingBase < x - y ∧
          x - y < coefficientEncodingBase)
      left right)
    (encoding :
      encodeCoefficientRow left = encodeCoefficientRow right) :
    left = right := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
      rename_i x y left right
      simp only [encodeCoefficientRow, List.foldr_cons] at encoding
      have hxy : x = y := by
        unfold coefficientEncodingBase at bound encoding
        omega
      subst y
      have htail :
          encodeCoefficientRow left = encodeCoefficientRow right := by
        have hmul :
            coefficientEncodingBase * encodeCoefficientRow left =
              coefficientEncodingBase * encodeCoefficientRow right :=
          add_left_cancel encoding
        norm_num [coefficientEncodingBase] at hmul
        omega
      exact congrArg (x :: ·) (ih htail)

private theorem encodeCoefficientRow_weighted_sum
    (rows : List α) (columns : List β)
    (weight : α → Int) (entry : α → β → Int) :
    encodeCoefficientRow
        (columns.map fun column =>
          (rows.map fun row => weight row * entry row column).sum) =
      (rows.map fun row =>
        weight row *
          encodeCoefficientRow
            (columns.map fun column => entry row column)).sum := by
  induction columns with
  | nil => simp [encodeCoefficientRow]
  | cons column columns ih =>
      simp only [List.map_cons, encodeCoefficientRow, List.foldr_cons]
      change
        (rows.map fun row => weight row * entry row column).sum +
            coefficientEncodingBase *
              encodeCoefficientRow
                (columns.map fun column =>
                  (rows.map fun row =>
                    weight row * entry row column).sum) =
          (rows.map fun row =>
            weight row *
              (entry row column +
                coefficientEncodingBase *
                  encodeCoefficientRow
                    (columns.map fun column =>
                      entry row column))).sum
      rw [ih]
      simp only [mul_add]
      rw [List.sum_map_add]
      congr 1
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro row hrow
      ring

private theorem encodeCoefficientRow_map_zero (entries : List α) :
    encodeCoefficientRow (entries.map fun _ => (0 : Int)) = 0 := by
  induction entries with
  | nil =>
      rfl
  | cons entry entries ih =>
      simp only [List.map_cons, encodeCoefficientRow, List.foldr_cons,
        zero_add]
      unfold encodeCoefficientRow at ih
      rw [ih, mul_zero]

private theorem encodeCoefficientRow_indicator (n k : Nat) :
    encodeCoefficientRow
        ((List.range n).map fun i =>
          if i = k then (1 : Int) else 0) =
      if k < n then coefficientEncodingBase ^ k else 0 := by
  induction n generalizing k with
  | zero =>
      simp [encodeCoefficientRow]
  | succ n ih =>
      rw [List.range_succ_eq_map]
      unfold encodeCoefficientRow at ih
      cases k with
      | zero =>
          simp only [List.map_cons, List.map_map, if_pos,
            encodeCoefficientRow, List.foldr_cons]
          change
            1 + coefficientEncodingBase *
                List.foldr
                  (fun entry result =>
                    entry + coefficientEncodingBase * result)
                  0 ((List.range n).map fun _ => (0 : Int)) =
              _
          have hzero := encodeCoefficientRow_map_zero (List.range n)
          unfold encodeCoefficientRow at hzero
          rw [hzero, mul_zero, add_zero]
          simp
      | succ k =>
          simp only [List.map_cons, List.map_map, Nat.zero_ne_add_one,
            ↓reduceIte, encodeCoefficientRow, List.foldr_cons]
          rw [show
            (List.range n).map
                ((fun i => if i = k + 1 then (1 : Int) else 0) ∘
                  Nat.succ) =
            (List.range n).map
                (fun i => if i = k then (1 : Int) else 0) by
            simp [Function.comp_def]]
          simp only [zero_add]
          rw [ih]
          simp only [Nat.add_lt_add_iff_right]
          split <;> rename_i hk
          · rw [pow_succ']
          · rw [mul_zero]

private theorem encodeCoefficientRow_keyIndicator
    (key block : Nat) :
    encodeCoefficientRow
        ((List.range 1000).map fun offset =>
          if block * 1000 + offset = key then (1 : Int) else 0) =
      if key / 1000 = block then
        coefficientEncodingBase ^ (key % 1000)
      else 0 := by
  split <;> rename_i hblock
  · have hoffset : key % 1000 < 1000 :=
      Nat.mod_lt _ (by norm_num)
    have hkey :
        block * 1000 + key % 1000 = key := by
      rw [← hblock]
      exact Nat.div_add_mod' key 1000
    rw [show
      (List.range 1000).map
          (fun offset =>
            if block * 1000 + offset = key then (1 : Int) else 0) =
        (List.range 1000).map
          (fun offset =>
            if offset = key % 1000 then (1 : Int) else 0) by
      apply List.map_congr_left
      intro offset hoffsetMem
      have hoffsetLt := List.mem_range.mp hoffsetMem
      congr 1
      apply propext
      constructor <;> intro h
      · omega
      · omega]
    rw [encodeCoefficientRow_indicator, if_pos hoffset]
  · rw [show
      (List.range 1000).map
          (fun offset =>
            if block * 1000 + offset = key then (1 : Int) else 0) =
        (List.range 1000).map (fun _ => (0 : Int)) by
      apply List.map_congr_left
      intro offset hoffsetMem
      have hoffsetLt := List.mem_range.mp hoffsetMem
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      intro heq
      have hdiv :
          (block * 1000 + offset) / 1000 = block := by
        rw [Nat.mul_comm block 1000,
          Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hoffsetLt,
          Nat.add_zero]
      rw [← heq] at hblock
      exact hblock hdiv]
    rw [encodeCoefficientRow_map_zero]

private def coefficientAt
    (terms : List (IntegerTableTerm 73033)) (key : Nat) : Int :=
  (terms.map fun term =>
    if term.key.val = key then term.numerator else 0).sum

private def coefficientRow
    (terms : List (IntegerTableTerm 73033)) (block : Nat) :
    List Int :=
  (List.range 1000).map fun offset =>
    coefficientAt terms (block * 1000 + offset)

private def coefficientBlockValue
    (terms : List (IntegerTableTerm 73033)) (block : Nat) : Int :=
  (terms.map fun term =>
    if term.key.val / 1000 = block then
      term.numerator *
        coefficientEncodingBase ^ (term.key.val % 1000)
    else 0).sum

private theorem encodeCoefficientRow_coefficientRow
    (terms : List (IntegerTableTerm 73033)) (block : Nat) :
    encodeCoefficientRow (coefficientRow terms block) =
      coefficientBlockValue terms block := by
  rw [show coefficientRow terms block =
      (List.range 1000).map fun offset =>
        (terms.map fun term =>
          term.numerator *
            if block * 1000 + offset = term.key.val then
              (1 : Int)
            else 0).sum by
    unfold coefficientRow coefficientAt
    apply List.map_congr_left
    intro offset hoffset
    apply congrArg List.sum
    apply List.map_congr_left
    intro term hterm
    by_cases hkey : term.key.val = block * 1000 + offset
    · simp [hkey]
    · simp [hkey, Ne.symm hkey]]
  rw [encodeCoefficientRow_weighted_sum]
  unfold coefficientBlockValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro term hterm
  rw [encodeCoefficientRow_keyIndicator]
  split <;> simp

private theorem coefficientCheckData_eq_foldl
    (terms : List (IntegerTableTerm 73033)) :
    coefficientCheckData terms =
      terms.foldl coefficientCheckStep
        (Array.replicate 74 (0 : Int), 0) := by
  rfl

private theorem coefficientCheckFold_size
    (terms : List (IntegerTableTerm 73033))
    (state : Array Int × Nat) :
    (terms.foldl coefficientCheckStep state).1.size =
      state.1.size := by
  induction terms generalizing state with
  | nil =>
      rfl
  | cons term terms ih =>
      rw [List.foldl_cons, ih]
      simp [coefficientCheckStep]

private theorem coefficientCheckFold_getElem
    (terms : List (IntegerTableTerm 73033))
    (state : Array Int × Nat) (block : Fin 74)
    (hsize : state.1.size = 74) :
    (terms.foldl coefficientCheckStep state).1.getD block.val 0 =
      state.1.getD block.val 0 +
        (terms.map fun term =>
          if term.key.val / 1000 = block.val then
            Int.shiftLeft term.numerator
              (64 * (term.key.val % 1000))
          else 0).sum := by
  induction terms generalizing state with
  | nil =>
      simp
  | cons term terms ih =>
      rw [List.foldl_cons, ih]
      · simp only [List.map_cons, List.sum_cons]
        unfold coefficientCheckStep
        have hvalid : block.val < state.1.size := by
          rw [hsize]
          exact block.isLt
        rw [Array.getD_eq_getD_getElem?,
          Array.getD_eq_getD_getElem?, Array.getElem?_modify,
          Array.getElem?_eq_getElem hvalid]
        simp only [Option.map_some, Option.getD_some]
        split <;> rename_i hblock
        · simp [add_assoc]
        · simp
      · simpa [coefficientCheckStep] using hsize

private theorem coefficientCheckFold_snd
    (terms : List (IntegerTableTerm 73033))
    (state : Array Int × Nat) :
    (terms.foldl coefficientCheckStep state).2 =
      state.2 +
        (terms.map fun term => term.numerator.natAbs).sum := by
  induction terms generalizing state with
  | nil =>
      simp
  | cons term terms ih =>
      rw [List.foldl_cons, ih]
      simp [coefficientCheckStep]
      omega

private theorem coefficientShift_eq
    (numerator : Int) (offset : Nat) :
    Int.shiftLeft numerator (64 * offset) =
      numerator * coefficientEncodingBase ^ offset := by
  change (numerator <<< (64 * offset)) =
    numerator * coefficientEncodingBase ^ offset
  rw [Int.shiftLeft_eq]
  have hbase : coefficientEncodingBase = (2 : Int) ^ 64 := by
    norm_num [coefficientEncodingBase]
  rw [hbase, pow_mul]

private theorem coefficientCheckData_getD
    (terms : List (IntegerTableTerm 73033)) (block : Fin 74) :
    (coefficientCheckData terms).1.getD block.val 0 =
      coefficientBlockValue terms block.val := by
  rw [coefficientCheckData_eq_foldl]
  calc
    (terms.foldl coefficientCheckStep
        (Array.replicate 74 (0 : Int), 0)).1.getD block.val 0 =
        (Array.replicate 74 (0 : Int)).getD block.val 0 +
          (terms.map fun term =>
            if term.key.val / 1000 = block.val then
              Int.shiftLeft term.numerator
                (64 * (term.key.val % 1000))
            else 0).sum :=
      coefficientCheckFold_getElem terms
        (Array.replicate 74 (0 : Int), 0) block (by simp)
    _ = coefficientBlockValue terms block.val := by
      simp only [Array.getD_eq_getD_getElem?,
        Array.getElem?_replicate, block.isLt, ↓reduceIte,
        Option.getD_some, zero_add]
      unfold coefficientBlockValue
      apply congrArg List.sum
      apply List.map_congr_left
      intro term hterm
      split <;> simp [coefficientShift_eq]

private theorem coefficientCheckData_snd
    (terms : List (IntegerTableTerm 73033)) :
    (coefficientCheckData terms).2 =
      (terms.map fun term => term.numerator.natAbs).sum := by
  rw [coefficientCheckData_eq_foldl,
    coefficientCheckFold_snd]
  simp

private theorem coefficientCheckData_encodes
    (terms : List (IntegerTableTerm 73033)) (block : Fin 74) :
    encodeCoefficientRow (coefficientRow terms block.val) =
      (coefficientCheckData terms).1.getD block.val 0 := by
  rw [encodeCoefficientRow_coefficientRow,
    coefficientCheckData_getD]

private theorem addCoefficientEncodingRowsList_getD
    (length index : Nat) (left right : List Int)
    (hindex : index < length) :
    (addCoefficientEncodingRowsList length left right).getD index 0 =
      left.getD index 0 + right.getD index 0 := by
  induction length generalizing index left right with
  | zero =>
      omega
  | succ length ih =>
      cases index with
      | zero =>
          cases left <;> cases right <;>
            simp [addCoefficientEncodingRowsList]
      | succ index =>
          have htail : index < length := by omega
          cases left <;> cases right <;>
            simp only [addCoefficientEncodingRowsList,
              List.getD_cons_succ]
          all_goals (rw [ih index _ _ htail] <;> simp)

private theorem addCoefficientEncodingRows_getD
    (left right : Array Int) (block : Fin 74) :
    (addCoefficientEncodingRows left right).getD block.val 0 =
      left.getD block.val 0 + right.getD block.val 0 := by
  simpa only [addCoefficientEncodingRows,
    Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD, Array.getElem?_toList] using
      addCoefficientEncodingRowsList_getD
        74 block.val left.toList right.toList block.isLt

private theorem sumCoefficientEncodingRowsFold_getD
    (rows : List (Array Int)) (state : Array Int) (block : Fin 74) :
    (rows.foldl addCoefficientEncodingRows state).getD block.val 0 =
      state.getD block.val 0 +
        (rows.map fun row => row.getD block.val 0).sum := by
  induction rows generalizing state with
  | nil =>
      simp
  | cons row rows ih =>
      rw [List.foldl_cons, ih, addCoefficientEncodingRows_getD]
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem sumCoefficientEncodingRows_getD
    (rows : List (Array Int)) (block : Fin 74) :
    (sumCoefficientEncodingRows rows).getD block.val 0 =
      (rows.map fun row => row.getD block.val 0).sum := by
  unfold sumCoefficientEncodingRows
  rw [sumCoefficientEncodingRowsFold_getD]
  simp [Array.getD_eq_getD_getElem?]

private theorem coefficientBlockValue_append
    (left right : List (IntegerTableTerm 73033)) (block : Nat) :
    coefficientBlockValue (left ++ right) block =
      coefficientBlockValue left block +
        coefficientBlockValue right block := by
  simp [coefficientBlockValue]

private theorem coefficientBlockValue_flatten
    (chunks : List (List (IntegerTableTerm 73033))) (block : Nat) :
    coefficientBlockValue chunks.flatten block =
      (chunks.map fun chunk =>
        coefficientBlockValue chunk block).sum := by
  induction chunks with
  | nil =>
      simp [coefficientBlockValue]
  | cons chunk chunks ih =>
      rw [List.flatten_cons, coefficientBlockValue_append,
        List.map_cons, List.sum_cons, ih]

private theorem sumCoefficientEncodingRows_map_checkData_getD
    (chunks : List (List (IntegerTableTerm 73033))) (block : Fin 74) :
    (sumCoefficientEncodingRows
        (chunks.map fun chunk => (coefficientCheckData chunk).1)).getD
          block.val 0 =
      coefficientBlockValue chunks.flatten block.val := by
  rw [sumCoefficientEncodingRows_getD,
    coefficientBlockValue_flatten]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro chunk hchunk
  exact coefficientCheckData_getD chunk block

private def coefficientAbsoluteTotal
    (terms : List (IntegerTableTerm 73033)) : Nat :=
  (terms.map fun term => term.numerator.natAbs).sum

private theorem coefficientAt_natAbs_le
    (terms : List (IntegerTableTerm 73033)) (key : Nat) :
    (coefficientAt terms key).natAbs ≤
      coefficientAbsoluteTotal terms := by
  induction terms with
  | nil =>
      simp [coefficientAt, coefficientAbsoluteTotal]
  | cons term terms ih =>
      unfold coefficientAt coefficientAbsoluteTotal
      simp only [List.map_cons, List.sum_cons]
      calc
        (ite (term.key.val = key) term.numerator 0 +
            (terms.map fun term : IntegerTableTerm 73033 =>
              if term.key.val = key then term.numerator else 0).sum).natAbs ≤
            (ite (term.key.val = key) term.numerator 0).natAbs +
              ((terms.map fun term : IntegerTableTerm 73033 =>
                if term.key.val = key then term.numerator else 0).sum).natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ term.numerator.natAbs +
              (terms.map fun term : IntegerTableTerm 73033 =>
                term.numerator.natAbs).sum := by
          apply Nat.add_le_add
          · split <;> simp
          · exact ih

private theorem coefficientDifferenceBounds
    (left right : List (IntegerTableTerm 73033)) (key : Nat)
    (hbound :
      coefficientAbsoluteTotal left +
          coefficientAbsoluteTotal right <
        18446744073709551616) :
    -coefficientEncodingBase <
        coefficientAt left key - coefficientAt right key ∧
      coefficientAt left key - coefficientAt right key <
        coefficientEncodingBase := by
  have hleft := coefficientAt_natAbs_le left key
  have hright := coefficientAt_natAbs_le right key
  have hdiff :
      (coefficientAt left key - coefficientAt right key).natAbs <
        18446744073709551616 := by
    calc
      (coefficientAt left key - coefficientAt right key).natAbs ≤
          (coefficientAt left key).natAbs +
            (coefficientAt right key).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ coefficientAbsoluteTotal left +
            coefficientAbsoluteTotal right :=
        Nat.add_le_add hleft hright
      _ < 18446744073709551616 := hbound
  have hdiffInt :
      ((coefficientAt left key -
        coefficientAt right key).natAbs : Int) <
          18446744073709551616 := by
    exact_mod_cast hdiff
  have hupp := Int.le_natAbs (a :=
    coefficientAt left key - coefficientAt right key)
  have hneg := Int.le_natAbs (a :=
    -(coefficientAt left key - coefficientAt right key))
  rw [Int.natAbs_neg] at hneg
  unfold coefficientEncodingBase
  omega

private theorem List.forall₂_map_same
    (entries : List α) (left : α → β) (right : α → γ)
    (relation : β → γ → Prop)
    (h : ∀ entry ∈ entries, relation (left entry) (right entry)) :
    List.Forall₂ relation (entries.map left) (entries.map right) := by
  induction entries with
  | nil =>
      exact .nil
  | cons entry entries ih =>
      exact .cons (h entry (by simp))
        (ih fun element helement =>
          h element (by simp [helement]))

private theorem coefficientRow_differenceBounds
    (left right : List (IntegerTableTerm 73033)) (block : Nat)
    (hbound :
      coefficientAbsoluteTotal left +
          coefficientAbsoluteTotal right <
        18446744073709551616) :
    List.Forall₂
      (fun x y =>
        -coefficientEncodingBase < x - y ∧
          x - y < coefficientEncodingBase)
      (coefficientRow left block) (coefficientRow right block) := by
  unfold coefficientRow
  apply List.forall₂_map_same
  intro offset hoffset
  exact coefficientDifferenceBounds left right
    (block * 1000 + offset) hbound

private theorem coefficientRow_eq_of_encoding_eq
    (left right : List (IntegerTableTerm 73033)) (block : Nat)
    (hbound :
      coefficientAbsoluteTotal left +
          coefficientAbsoluteTotal right <
        18446744073709551616)
    (hencoding :
      encodeCoefficientRow (coefficientRow left block) =
        encodeCoefficientRow (coefficientRow right block)) :
    coefficientRow left block = coefficientRow right block :=
  encodeCoefficientRow_injective_of_difference_bound
    (coefficientRow_differenceBounds left right block hbound)
    hencoding

private theorem interpretIntegerTerms_eq_sum_coefficients
    {M : Type*} [AddCommMonoid M] [Module Rat M]
    (atom : Fin 73033 → M)
    (terms : List (IntegerTableTerm 73033)) :
    interpretIntegerTerms atom terms =
      ∑ key : Fin 73033,
        (coefficientAt terms key.val : Rat) • atom key := by
  induction terms with
  | nil =>
      simp [interpretIntegerTerms, coefficientAt]
  | cons term terms ih =>
      calc
        interpretIntegerTerms atom (term :: terms) =
            (term.numerator : Rat) • atom term.key +
              interpretIntegerTerms atom terms := by
          simp [interpretIntegerTerms]
        _ = (term.numerator : Rat) • atom term.key +
              ∑ key : Fin 73033,
                (coefficientAt terms key.val : Rat) • atom key := by
          rw [ih]
        _ = ∑ key : Fin 73033,
              (coefficientAt (term :: terms) key.val : Rat) •
                atom key := by
          unfold coefficientAt
          simp only [List.map_cons, List.sum_cons, Int.cast_add,
            add_smul, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single term.key]
          · simp
          · intro key hkey hne
            have hval : term.key.val ≠ key.val := by
              intro heq
              apply hne
              exact Fin.ext heq.symm
            simp [hval]
          · simp

private theorem interpretIntegerTerms_eq_of_coefficients
    {M : Type*} [AddCommMonoid M] [Module Rat M]
    (atom : Fin 73033 → M)
    (left right : List (IntegerTableTerm 73033))
    (hcoeff :
      ∀ key : Fin 73033,
        coefficientAt left key.val =
          coefficientAt right key.val) :
    interpretIntegerTerms atom left =
      interpretIntegerTerms atom right := by
  rw [interpretIntegerTerms_eq_sum_coefficients,
    interpretIntegerTerms_eq_sum_coefficients]
  apply Finset.sum_congr rfl
  intro key hkey
  rw [hcoeff key]

private theorem coefficientRow_getD
    (terms : List (IntegerTableTerm 73033)) (key : Nat) :
    (coefficientRow terms (key / 1000)).getD (key % 1000) 0 =
      coefficientAt terms key := by
  have hoffset : key % 1000 < 1000 :=
    Nat.mod_lt _ (by norm_num)
  unfold coefficientRow
  rw [List.getD_eq_getElem _ _ (by simpa using hoffset)]
  simp only [List.getElem_map, List.getElem_range]
  rw [Nat.div_add_mod' key 1000]

private theorem coefficients_eq_of_rows
    (left right : List (IntegerTableTerm 73033))
    (hrows :
      ∀ block : Fin 74,
        coefficientRow left block.val =
          coefficientRow right block.val) :
    ∀ key : Fin 73033,
      coefficientAt left key.val =
        coefficientAt right key.val := by
  intro key
  have hblock : key.val / 1000 < 74 := by
    apply Nat.div_lt_of_lt_mul
    omega
  let block : Fin 74 := ⟨key.val / 1000, hblock⟩
  have hrow := hrows block
  have hget := congrArg
    (fun row : List Int => row.getD (key.val % 1000) 0) hrow
  dsimp [block] at hget
  rw [coefficientRow_getD left key.val,
    coefficientRow_getD right key.val] at hget
  exact hget

private theorem range_map_getD
    {α : Type*} (entries : List α) (fallback : α) :
    (List.range entries.length).map
        (fun index => entries.getD index fallback) =
      entries := by
  induction entries with
  | nil =>
      rfl
  | cons entry entries ih =>
      change
        (List.range (entries.length + 1)).map
            (fun index => (entry :: entries).getD index fallback) =
          entry :: entries
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.getD_cons_zero, List.map_map]
      change
        entry ::
            (List.range entries.length).map
              (fun index => entries.getD index fallback) =
          entry :: entries
      exact congrArg (entry :: ·) ih

private theorem coefficientSourceChunks_length :
    coefficientSourceChunks.length = 82 := by
  unfold coefficientSourceChunks coefficientFactorTermChunks
  decide +kernel

private theorem coefficientSourceEncodingRows_length :
    coefficientSourceEncodingRows.length = 82 := by
  unfold coefficientSourceEncodingRows
  rfl

private theorem coefficientSourceAbsoluteTotals_length :
    coefficientSourceAbsoluteTotals.length = 82 := by
  unfold coefficientSourceAbsoluteTotals
  rfl

private theorem coefficientSourceChunks_range :
    (List.range 82).map coefficientSourceChunk =
      coefficientSourceChunks := by
  unfold coefficientSourceChunk
  rw [← coefficientSourceChunks_length]
  exact range_map_getD coefficientSourceChunks []

private theorem coefficientSourceEncodingRows_eq :
    coefficientSourceChunks.map
        (fun chunk => (coefficientCheckData chunk).1) =
      coefficientSourceEncodingRows := by
  calc
    coefficientSourceChunks.map
        (fun chunk => (coefficientCheckData chunk).1) =
        ((List.range 82).map coefficientSourceChunk).map
          (fun chunk => (coefficientCheckData chunk).1) := by
      rw [coefficientSourceChunks_range]
    _ = (List.range 82).map
          (fun index =>
            (coefficientCheckData
              (coefficientSourceChunk index)).1) := by
      rw [List.map_map]
    _ = (List.range 82).map
          (fun index =>
            coefficientSourceEncodingRows.getD index #[]) := by
      apply List.map_congr_left
      intro index hindex
      exact congrArg Prod.fst
        (allCoefficientEncodingLeafChecks
          ⟨index, List.mem_range.mp hindex⟩)
    _ = coefficientSourceEncodingRows := by
      rw [← coefficientSourceEncodingRows_length]
      exact range_map_getD coefficientSourceEncodingRows #[]

private theorem coefficientSourceAbsoluteTotals_eq :
    coefficientSourceChunks.map coefficientAbsoluteTotal =
      coefficientSourceAbsoluteTotals := by
  calc
    coefficientSourceChunks.map coefficientAbsoluteTotal =
        ((List.range 82).map coefficientSourceChunk).map
          coefficientAbsoluteTotal := by
      rw [coefficientSourceChunks_range]
    _ = (List.range 82).map
          (fun index =>
            coefficientAbsoluteTotal
              (coefficientSourceChunk index)) := by
      rw [List.map_map]
    _ = (List.range 82).map
          (fun index =>
            coefficientSourceAbsoluteTotals.getD index 0) := by
      apply List.map_congr_left
      intro index hindex
      have hcheck := congrArg Prod.snd
        (allCoefficientEncodingLeafChecks
          ⟨index, List.mem_range.mp hindex⟩)
      rw [coefficientCheckData_snd] at hcheck
      exact hcheck
    _ = coefficientSourceAbsoluteTotals := by
      rw [← coefficientSourceAbsoluteTotals_length]
      exact range_map_getD coefficientSourceAbsoluteTotals 0

private theorem coefficientAbsoluteTotal_append
    (left right : List (IntegerTableTerm 73033)) :
    coefficientAbsoluteTotal (left ++ right) =
      coefficientAbsoluteTotal left +
        coefficientAbsoluteTotal right := by
  simp [coefficientAbsoluteTotal]

private theorem coefficientAbsoluteTotal_flatten
    (chunks : List (List (IntegerTableTerm 73033))) :
    coefficientAbsoluteTotal chunks.flatten =
      (chunks.map coefficientAbsoluteTotal).sum := by
  induction chunks with
  | nil =>
      simp [coefficientAbsoluteTotal]
  | cons chunk chunks ih =>
      rw [List.flatten_cons, coefficientAbsoluteTotal_append,
        List.map_cons, List.sum_cons, ih]

private theorem coefficientSourceAbsoluteTotal :
    coefficientAbsoluteTotal certificateTerms =
      coefficientSourceAbsoluteTotals.sum := by
  rw [← coefficientSourceChunks_flatten,
    coefficientAbsoluteTotal_flatten,
    coefficientSourceAbsoluteTotals_eq]

private theorem coefficientTargetAbsoluteTotal :
    coefficientAbsoluteTotal targetTerms =
      18435840000000000 := by
  have hcheck := congrArg Prod.snd coefficientTargetEncodingCheck
  rw [coefficientCheckData_snd] at hcheck
  exact hcheck

private theorem coefficientEncodingEquality (block : Fin 74) :
    encodeCoefficientRow
        (coefficientRow certificateTerms block.val) =
      encodeCoefficientRow
        (coefficientRow targetTerms block.val) := by
  have haggregate := coefficientEncodingAggregateCheck.1
  calc
    encodeCoefficientRow
        (coefficientRow certificateTerms block.val) =
        coefficientBlockValue certificateTerms block.val :=
      encodeCoefficientRow_coefficientRow certificateTerms block.val
    _ = coefficientBlockValue
          coefficientSourceChunks.flatten block.val := by
      rw [coefficientSourceChunks_flatten]
    _ = (sumCoefficientEncodingRows
          (coefficientSourceChunks.map fun chunk =>
            (coefficientCheckData chunk).1)).getD block.val 0 :=
      (sumCoefficientEncodingRows_map_checkData_getD
        coefficientSourceChunks block).symm
    _ = (sumCoefficientEncodingRows
          coefficientSourceEncodingRows).getD block.val 0 := by
      rw [coefficientSourceEncodingRows_eq]
    _ = coefficientTargetEncoding.getD block.val 0 := by
      rw [haggregate]
    _ = (coefficientCheckData targetTerms).1.getD block.val 0 := by
      rw [coefficientTargetEncodingCheck]
    _ = encodeCoefficientRow
          (coefficientRow targetTerms block.val) :=
      (coefficientCheckData_encodes targetTerms block).symm

private theorem coefficientRowsEquality :
    ∀ block : Fin 74,
      coefficientRow certificateTerms block.val =
        coefficientRow targetTerms block.val := by
  intro block
  apply coefficientRow_eq_of_encoding_eq
  · rw [coefficientSourceAbsoluteTotal,
      coefficientTargetAbsoluteTotal]
    exact coefficientEncodingAggregateCheck.2
  · exact coefficientEncodingEquality block

theorem coefficientIdentity_sound
    {M : Type*} [AddCommMonoid M] [Module Rat M]
    (atom : Fin 73033 → M) :
    interpretIntegerTerms atom certificateTerms =
      interpretIntegerTerms atom targetTerms := by
  apply interpretIntegerTerms_eq_of_coefficients
  exact coefficients_eq_of_rows certificateTerms targetTerms
    coefficientRowsEquality

end AffineSymplecticCertificate

end ConnesRigidity

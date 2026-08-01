


import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring














namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

set_option maxRecDepth 1000000


def orbitRadixBase : ℤ := 4722366482869645213696


def orbitRadixEncode (digits : List ℤ) : ℤ :=
  digits.foldr (fun digit encoded => digit + orbitRadixBase * encoded) 0

@[simp] theorem orbitRadixEncode_nil : orbitRadixEncode [] = 0 := rfl

@[simp] theorem orbitRadixEncode_cons (digit : ℤ) (digits : List ℤ) :
    orbitRadixEncode (digit :: digits) =
      digit + orbitRadixBase * orbitRadixEncode digits := rfl



theorem orbitRadixEncode_injective_of_difference_bound
    {left right : List ℤ}
    (bounds : List.Forall₂
      (fun x y => -orbitRadixBase < x - y ∧ x - y < orbitRadixBase)
      left right)
    (encoding : orbitRadixEncode left = orbitRadixEncode right) :
    left = right := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
      rename_i x y left right
      simp only [orbitRadixEncode_cons] at encoding
      have hxy : x = y := by
        unfold orbitRadixBase at bound encoding
        omega
      subst y
      have htail : orbitRadixEncode left = orbitRadixEncode right := by
        have hmul :
            orbitRadixBase * orbitRadixEncode left =
              orbitRadixBase * orbitRadixEncode right :=
          add_left_cancel encoding
        norm_num [orbitRadixBase] at hmul
        omega
      rw [ih htail]



theorem orbitRadixEncode_injective_of_abs_difference_bound
    {left right : List ℤ}
    (bounds : List.Forall₂
      (fun x y => |x - y| < orbitRadixBase) left right)
    (encoding : orbitRadixEncode left = orbitRadixEncode right) :
    left = right := by
  have differenceBounds := bounds.imp
    (fun _ _ bound => abs_lt.mp bound)
  exact orbitRadixEncode_injective_of_difference_bound differenceBounds encoding


theorem orbitRadixEncode_weighted_sum
    (rows : List α) (columns : List β)
    (weight : α → ℤ) (entry : α → β → ℤ) :
    orbitRadixEncode
        (columns.map fun column =>
          (rows.map fun row => weight row * entry row column).sum) =
      (rows.map fun row =>
        weight row *
          orbitRadixEncode (columns.map fun column => entry row column)).sum := by
  induction columns with
  | nil => simp [orbitRadixEncode]
  | cons column columns ih =>
      simp only [List.map_cons, orbitRadixEncode_cons]
      rw [ih]
      simp only [mul_add]
      rw [List.sum_map_add]
      congr 1
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro row _
      ring




theorem orbitRadixEncode_fin_weighted_sum
    {rowCount : Nat} (columns : List β)
    (weight : Fin rowCount → ℤ) (entry : Fin rowCount → β → ℤ) :
    orbitRadixEncode
        (columns.map fun column =>
          ∑ row : Fin rowCount, weight row * entry row column) =
      ∑ row : Fin rowCount,
        weight row *
          orbitRadixEncode (columns.map fun column => entry row column) := by
  simp_rw [Fin.sum_univ_def]
  exact orbitRadixEncode_weighted_sum (List.finRange rowCount)
    columns weight entry



theorem orbitRadix_finRange_map_val
    {count : Nat} (entry : Nat → ℤ) :
    (List.finRange count).map (fun index => entry index.val) =
      (List.range count).map entry := by
  change (List.finRange count).map
      (entry ∘ (fun index : Fin count => (index : Nat))) = _
  rw [← List.map_map, List.map_coe_finRange_eq_range]



theorem orbitRadixEncode_map_mul (scale : ℤ) (digits : List ℤ) :
    orbitRadixEncode (digits.map fun digit => scale * digit) =
      scale * orbitRadixEncode digits := by
  induction digits with
  | nil => simp
  | cons digit digits ih =>
      simp only [List.map_cons, orbitRadixEncode_cons, ih]
      ring


theorem orbitRadixEncode_map_add
    (columns : List α) (left right : α → ℤ) :
    orbitRadixEncode (columns.map fun column => left column + right column) =
      orbitRadixEncode (columns.map left) +
        orbitRadixEncode (columns.map right) := by
  induction columns with
  | nil => simp
  | cons column columns ih =>
      simp only [List.map_cons, orbitRadixEncode_cons, ih]
      ring


theorem orbitRadixEncode_map_sub
    (columns : List α) (left right : α → ℤ) :
    orbitRadixEncode (columns.map fun column => left column - right column) =
      orbitRadixEncode (columns.map left) -
        orbitRadixEncode (columns.map right) := by
  induction columns with
  | nil => simp
  | cons column columns ih =>
      simp only [List.map_cons, orbitRadixEncode_cons, ih]
      ring



theorem orbitRadix_weighted_entries_eq_of_packed
    (rows : List α) (columns : List β)
    (weight : α → ℤ) (entry : α → β → ℤ) (target : β → ℤ)
    (encoding :
      (rows.map fun row =>
        weight row *
          orbitRadixEncode (columns.map fun column => entry row column)).sum =
        orbitRadixEncode (columns.map target))
    (bounds : ∀ column ∈ columns,
      -orbitRadixBase <
          (rows.map fun row => weight row * entry row column).sum -
            target column ∧
        (rows.map fun row => weight row * entry row column).sum -
            target column < orbitRadixBase) :
    ∀ column ∈ columns,
      (rows.map fun row => weight row * entry row column).sum =
        target column := by
  have digitBounds : List.Forall₂
      (fun x y => -orbitRadixBase < x - y ∧ x - y < orbitRadixBase)
      (columns.map fun column =>
        (rows.map fun row => weight row * entry row column).sum)
      (columns.map target) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    exact bounds
  have digitEquality :
      (columns.map fun column =>
        (rows.map fun row => weight row * entry row column).sum) =
        columns.map target := by
    apply orbitRadixEncode_injective_of_difference_bound digitBounds
    rw [orbitRadixEncode_weighted_sum]
    exact encoding
  intro column hcolumn
  have mappedEquality : List.Forall₂ (fun x y : ℤ => x = y)
      (columns.map fun column =>
        (rows.map fun row => weight row * entry row column).sum)
      (columns.map target) := by
    rw [digitEquality]
    exact List.forall₂_refl _
  have equalityByColumn :
      List.Forall₂ (fun x y =>
        (rows.map fun row => weight row * entry row x).sum = target y)
        columns columns := by
    exact List.forall₂_map_right_iff.mp
      (List.forall₂_map_left_iff.mp mappedEquality)
  exact (List.forall₂_same.mp equalityByColumn) column hcolumn




theorem orbitRadix_abs_weighted_sum_le
    (rows : List α) (weight entry : α → ℤ) :
    |(rows.map fun row => weight row * entry row).sum| ≤
      (rows.map fun row => |weight row| * |entry row|).sum := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        |weight row * entry row +
            (rows.map fun row => weight row * entry row).sum| ≤
            |weight row * entry row| +
              |(rows.map fun row => weight row * entry row).sum| :=
          abs_add_le _ _
        _ ≤ |weight row| * |entry row| +
            (rows.map fun row => |weight row| * |entry row|).sum := by
          rw [abs_mul]
          exact add_le_add_right ih _



theorem orbitRadix_difference_bound_of_abs_add_lt
    (computed target : ℤ)
    (bound : |computed| + |target| < orbitRadixBase) :
    -orbitRadixBase < computed - target ∧
      computed - target < orbitRadixBase := by
  apply abs_lt.mp
  calc
    |computed - target| = |computed + -target| := by rw [sub_eq_add_neg]
    _ ≤ |computed| + |-target| := abs_add_le _ _
    _ = |computed| + |target| := by rw [abs_neg]
    _ < orbitRadixBase := bound



theorem orbitRadix_weighted_difference_bound
    (rows : List α) (weight entry : α → ℤ) (target : ℤ)
    (bound :
      (rows.map fun row => |weight row| * |entry row|).sum + |target| <
        orbitRadixBase) :
    -orbitRadixBase <
        (rows.map fun row => weight row * entry row).sum - target ∧
      (rows.map fun row => weight row * entry row).sum - target <
        orbitRadixBase := by
  apply orbitRadix_difference_bound_of_abs_add_lt
  calc
    |(rows.map fun row => weight row * entry row).sum| + |target| ≤
        (rows.map fun row => |weight row| * |entry row|).sum + |target| :=
      add_le_add_left (orbitRadix_abs_weighted_sum_le rows weight entry) _
    _ < orbitRadixBase := bound




theorem orbitRadix_two_stage_entries_eq_of_packed
    (rows : List α) (columns : List β) (innerRows : α → List γ)
    (leftWeight : α → ℤ)
    (middleWeight : α → γ → ℤ)
    (rightEntry : γ → β → ℤ) (target : β → ℤ)
    (encoding :
      (rows.map fun row =>
        leftWeight row *
          ((innerRows row).map fun inner =>
            middleWeight row inner *
              orbitRadixEncode
                (columns.map fun column => rightEntry inner column)).sum).sum =
        orbitRadixEncode (columns.map target))
    (bounds : ∀ column ∈ columns,
      let computed :=
        (rows.map fun row =>
          leftWeight row *
            ((innerRows row).map fun inner =>
              middleWeight row inner * rightEntry inner column).sum).sum
      |computed| + |target column| < orbitRadixBase) :
    ∀ column ∈ columns,
      (rows.map fun row =>
        leftWeight row *
          ((innerRows row).map fun inner =>
            middleWeight row inner * rightEntry inner column).sum).sum =
        target column := by
  apply orbitRadix_weighted_entries_eq_of_packed
    rows columns leftWeight
    (fun row column =>
      ((innerRows row).map fun inner =>
        middleWeight row inner * rightEntry inner column).sum)
    target
  · simp_rw [orbitRadixEncode_weighted_sum]
    exact encoding
  · intro column hcolumn
    exact orbitRadix_difference_bound_of_abs_add_lt _ _
      (bounds column hcolumn)



theorem orbitRadixEncode_finset_weighted_sum
    (rows : Finset α) (columns : List β)
    (weight : α → ℤ) (entry : α → β → ℤ) :
    orbitRadixEncode
        (columns.map fun column =>
          ∑ row ∈ rows, weight row * entry row column) =
      ∑ row ∈ rows,
        weight row *
          orbitRadixEncode (columns.map fun column => entry row column) := by
  classical
  induction rows using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      induction columns with
      | nil => rfl
      | cons column columns ih =>
          simpa only [List.map_cons, orbitRadixEncode_cons, mul_zero,
            add_zero, zero_add] using congrArg
              (fun value : ℤ => orbitRadixBase * value) ih
  | @insert row rows hrow ih =>
      simp only [Finset.sum_insert hrow]
      rw [orbitRadixEncode_map_add]
      have headEncoding :
          orbitRadixEncode
              (columns.map fun column => weight row * entry row column) =
            weight row *
              orbitRadixEncode
                (columns.map fun column => entry row column) := by
        simpa [List.map_map, Function.comp_def] using
          orbitRadixEncode_map_mul (weight row)
            (columns.map fun column => entry row column)
      rw [headEncoding, ih]


theorem orbitRadixEncode_finset_sum
    (rows : Finset α) (columns : List β)
    (entry : α → β → ℤ) :
    orbitRadixEncode
        (columns.map fun column => ∑ row ∈ rows, entry row column) =
      ∑ row ∈ rows,
        orbitRadixEncode (columns.map fun column => entry row column) := by
  simpa using orbitRadixEncode_finset_weighted_sum rows columns
    (fun _ => 1) entry

end ConnesRigidity.AffineSymplecticOrbitCertificate

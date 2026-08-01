


import ConnesRigidity.PropertyTExactCertificateCoefficientChecker
import Lean.Elab.Tactic.Omega







namespace ConnesRigidity

namespace AffineSymplecticCertificate

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

private theorem coefficientCheckFold_getD
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
        split
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

private theorem coefficientCheckData_size
    (terms : List (IntegerTableTerm 73033)) :
    (coefficientCheckData terms).1.size = 74 := by
  rw [coefficientCheckData_eq_foldl,
    coefficientCheckFold_size]
  simp

private theorem coefficientCheckData_getD
    (terms : List (IntegerTableTerm 73033)) (block : Fin 74) :
    (coefficientCheckData terms).1.getD block.val 0 =
      (terms.map fun term =>
        if term.key.val / 1000 = block.val then
          Int.shiftLeft term.numerator
            (64 * (term.key.val % 1000))
        else 0).sum := by
  rw [coefficientCheckData_eq_foldl,
    coefficientCheckFold_getD (hsize := by simp)]
  simp [Array.getD_eq_getD_getElem?]

private theorem coefficientCheckData_snd
    (terms : List (IntegerTableTerm 73033)) :
    (coefficientCheckData terms).2 =
      (terms.map fun term => term.numerator.natAbs).sum := by
  rw [coefficientCheckData_eq_foldl,
    coefficientCheckFold_snd]
  simp

private theorem addCoefficientEncodingRows_size
    (left right : Array Int) :
    (addCoefficientEncodingRows left right).size = 74 := by
  suffices
      (addCoefficientEncodingRowsList 74
        left.toList right.toList).length = 74 by
    simpa [addCoefficientEncodingRows] using this
  generalize 74 = length
  induction length generalizing left right with
  | zero =>
      rfl
  | succ length ih =>
      cases hleft : left.toList <;>
        cases hright : right.toList <;>
        simp [addCoefficientEncodingRowsList, ih]

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

private theorem array_eq_of_size_and_getD
    (left right : Array Int)
    (hleft : left.size = 74) (hright : right.size = 74)
    (hget :
      ∀ block : Fin 74,
        left.getD block.val 0 = right.getD block.val 0) :
    left = right := by
  apply Array.ext_getElem?
  intro index
  by_cases hindex : index < 74
  · have hleftIndex : index < left.size := by
      simpa [hleft] using hindex
    have hrightIndex : index < right.size := by
      simpa [hright] using hindex
    have hvalue := hget ⟨index, hindex⟩
    rw [Array.getD_eq_getD_getElem?,
      Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hleftIndex,
      Array.getElem?_eq_getElem hrightIndex] at hvalue
    simp only [Option.getD_some] at hvalue
    simp [hleftIndex, hrightIndex, hvalue]
  · have hleftIndex : left.size ≤ index := by
      rw [hleft]
      exact Nat.le_of_not_gt hindex
    have hrightIndex : right.size ≤ index := by
      rw [hright]
      exact Nat.le_of_not_gt hindex
    rw [Array.getElem?_eq_none hleftIndex,
      Array.getElem?_eq_none hrightIndex]


theorem coefficientCheckData_append
    (left right : List (IntegerTableTerm 73033)) :
    coefficientCheckData (left ++ right) =
      (addCoefficientEncodingRows
          (coefficientCheckData left).1
          (coefficientCheckData right).1,
        (coefficientCheckData left).2 +
          (coefficientCheckData right).2) := by
  apply Prod.ext
  · apply array_eq_of_size_and_getD
    · exact coefficientCheckData_size (left ++ right)
    · exact addCoefficientEncodingRows_size _ _
    · intro block
      rw [coefficientCheckData_getD,
        addCoefficientEncodingRows_getD,
        coefficientCheckData_getD,
        coefficientCheckData_getD, List.map_append,
        List.sum_append]
  · rw [coefficientCheckData_snd,
      coefficientCheckData_snd, coefficientCheckData_snd,
      List.map_append, List.sum_append]

end AffineSymplecticCertificate

end ConnesRigidity

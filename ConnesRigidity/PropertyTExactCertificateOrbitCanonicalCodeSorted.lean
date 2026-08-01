


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalData
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalArrayGetD
import Mathlib.Data.List.GetD
import Mathlib.Order.Fin.Basic










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000


def coefficientCanonicalSortedRowsCheck : List (List Int) → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first.getD 1 0 < second.getD 1 0) &&
        coefficientCanonicalSortedRowsCheck (second :: rest)



def coefficientCanonicalIndexRowsCheck (sorted : Array (List Int)) :
    Nat → List (List Int) → List (List Int) → Bool
  | _, [], [] => true
  | orbit, witness :: witnesses, index :: indices =>
      let position := index.getD 0 0
      let sortedRow := sorted.getD position.toNat []
      decide (index.length = 1) &&
        decide (0 ≤ position ∧ position < (sorted.size : Int)) &&
        decide (sortedRow.getD 0 0 = (orbit : Int)) &&
        decide (sortedRow.getD 1 0 = witness.getD 1 0) &&
        coefficientCanonicalIndexRowsCheck sorted
          (orbit + 1) witnesses indices
  | _, _, _ => false


theorem coefficientCanonicalSortedRowsCheck_valid :
    coefficientCanonicalSortedRowsCheck
      coefficientCanonicalCodeSortedData = true := by
  decide +kernel



theorem coefficientCanonicalIndexRowsCheck_valid :
    coefficientCanonicalIndexRowsCheck
      coefficientCanonicalCodeSortedData.toArray 0
      coefficientCanonicalWitnessData
      coefficientCanonicalCodeIndexData = true := by
  decide +kernel


theorem coefficientCanonicalCodeData_lengths :
    coefficientCanonicalWitnessData.length = 995 ∧
      coefficientCanonicalCodeSortedData.length = 995 ∧
      coefficientCanonicalCodeIndexData.length = 995 := by
  decide +kernel


theorem coefficientCanonicalSortedRowsCheck_getD
    (rows : List (List Int)) (index : Nat)
    (hindex : index + 1 < rows.length)
    (hcheck : coefficientCanonicalSortedRowsCheck rows = true) :
    (rows.getD index []).getD 1 0 <
      (rows.getD (index + 1) []).getD 1 0 := by
  induction rows generalizing index with
  | nil => simp at hindex
  | cons first rest ih =>
      cases rest with
      | nil => simp at hindex
      | cons second tail =>
          simp only [coefficientCanonicalSortedRowsCheck,
            Bool.and_eq_true, decide_eq_true_eq] at hcheck
          cases index with
          | zero => simpa using hcheck.1
          | succ index =>
              simpa using ih index (by simpa using hindex) hcheck.2



theorem coefficientCanonicalSortedCode_strictMono :
    StrictMono (fun position : Fin 995 =>
      (coefficientCanonicalCodeSortedData.getD position.val []).getD 1 0) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro position
  apply coefficientCanonicalSortedRowsCheck_getD
    coefficientCanonicalCodeSortedData position.val
  · rw [coefficientCanonicalCodeData_lengths.2.1]
    exact Nat.succ_lt_succ position.isLt
  · exact coefficientCanonicalSortedRowsCheck_valid



theorem coefficientCanonicalIndexRowsCheck_getD
    (sorted : Array (List Int))
    (witnesses indices : List (List Int)) (start index : Nat)
    (hindex : index < witnesses.length)
    (hlength : witnesses.length = indices.length)
    (hcheck : coefficientCanonicalIndexRowsCheck sorted start
      witnesses indices = true) :
    let position := (indices.getD index []).getD 0 0
    position.toNat < sorted.size ∧
      (sorted.getD position.toNat []).getD 0 0 = (start + index : Nat) ∧
      (sorted.getD position.toNat []).getD 1 0 =
        (witnesses.getD index []).getD 1 0 := by
  induction witnesses generalizing indices start index with
  | nil => simp at hindex
  | cons witness witnesses ih =>
      cases indices with
      | nil => simp at hlength
      | cons position positions =>
          simp only [coefficientCanonicalIndexRowsCheck,
            Bool.and_eq_true, decide_eq_true_eq] at hcheck
          rcases hcheck with
            ⟨⟨⟨⟨_hrow, hposition⟩, hlabel⟩, hcode⟩, htail⟩
          cases index with
          | zero =>
              simp only [List.getD]
              exact ⟨(Int.toNat_lt hposition.1).mpr hposition.2,
                by simpa using hlabel,
                hcode⟩
          | succ index =>
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih positions (start + 1) index
                  (by simpa using hindex)
                  (by simpa using hlength)
                  htail




theorem coefficientCanonicalCodeRow_injective
    (first second : Fin 995)
    (hcode :
      (coefficientCanonicalWitnessData.getD first.val []).getD 1 0 =
        (coefficientCanonicalWitnessData.getD second.val []).getD 1 0) :
    first = second := by
  let sorted := coefficientCanonicalCodeSortedData.toArray
  have hfirst := coefficientCanonicalIndexRowsCheck_getD
    sorted coefficientCanonicalWitnessData
      coefficientCanonicalCodeIndexData 0 first.val
      (by simp [coefficientCanonicalCodeData_lengths.1])
      (by rw [coefficientCanonicalCodeData_lengths.1,
        coefficientCanonicalCodeData_lengths.2.2])
      coefficientCanonicalIndexRowsCheck_valid
  have hsecond := coefficientCanonicalIndexRowsCheck_getD
    sorted coefficientCanonicalWitnessData
      coefficientCanonicalCodeIndexData 0 second.val
      (by simp [coefficientCanonicalCodeData_lengths.1])
      (by rw [coefficientCanonicalCodeData_lengths.1,
        coefficientCanonicalCodeData_lengths.2.2])
      coefficientCanonicalIndexRowsCheck_valid
  let firstPosition : Fin 995 :=
    ⟨((coefficientCanonicalCodeIndexData.getD first.val []).getD 0 0).toNat,
      by simpa [sorted, coefficientCanonicalCodeData_lengths.2.1]
        using hfirst.1⟩
  let secondPosition : Fin 995 :=
    ⟨((coefficientCanonicalCodeIndexData.getD second.val []).getD 0 0).toNat,
      by simpa [sorted, coefficientCanonicalCodeData_lengths.2.1]
        using hsecond.1⟩
  have hsortedCode :
      (coefficientCanonicalCodeSortedData.getD firstPosition.val []).getD 1 0 =
        (coefficientCanonicalCodeSortedData.getD secondPosition.val []).getD 1 0 := by
    rw [← coefficientCanonical_toArray_getD,
      ← coefficientCanonical_toArray_getD]
    exact hfirst.2.2.trans (hcode.trans hsecond.2.2.symm)
  have hposition : firstPosition = secondPosition :=
    coefficientCanonicalSortedCode_strictMono.injective hsortedCode
  apply Fin.ext
  have hlabel : (first.val : Int) = (second.val : Int) := by
    calc
      (first.val : Int) =
          (sorted.getD firstPosition.val []).getD 0 0 := by
            simpa [firstPosition] using hfirst.2.1.symm
      _ = (sorted.getD secondPosition.val []).getD 0 0 := by
            rw [hposition]
      _ = (second.val : Int) := by
            simpa [secondPosition] using hsecond.2.1
  exact_mod_cast hlabel

end ConnesRigidity.AffineSymplecticOrbitCertificate

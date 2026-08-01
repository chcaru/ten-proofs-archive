


import ConnesRigidity.PropertyTExactCertificateGramBase
import ConnesRigidity.PropertyTExactCertificateGramColumnSoundness
import ConnesRigidity.PropertyTExactCertificateGramFactorRowSoundness
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring









namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

noncomputable section

private theorem encodeGramRow_injective_of_difference_bound
    {left right : List ℤ}
    (bounds : List.Forall₂
      (fun x y ↦ -gramEncodingBase < x - y ∧
        x - y < gramEncodingBase) left right)
    (encoding : encodeGramRow left = encodeGramRow right) :
    left = right := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
      rename_i x y left right
      simp only [encodeGramRow, List.foldr_cons] at encoding
      have hxy : x = y := by
        unfold gramEncodingBase at bound encoding
        omega
      subst y
      have htail : encodeGramRow left = encodeGramRow right := by
        have hmul :
            gramEncodingBase * encodeGramRow left =
              gramEncodingBase * encodeGramRow right :=
          add_left_cancel encoding
        norm_num [gramEncodingBase] at hmul
        omega
      rw [ih htail]

private theorem encodeGramRow_weighted_sum
    (rows : List α) (columns : List β)
    (weight : α → ℤ) (entry : α → β → ℤ) :
    encodeGramRow
        (columns.map fun column ↦
          (rows.map fun row ↦ weight row * entry row column).sum) =
      (rows.map fun row ↦
        weight row *
          encodeGramRow (columns.map fun column ↦ entry row column)).sum := by
  induction columns with
  | nil => simp [encodeGramRow]
  | cons column columns ih =>
      simp only [List.map_cons, encodeGramRow, List.foldr_cons]
      change
        (rows.map fun row ↦ weight row * entry row column).sum +
            gramEncodingBase *
              encodeGramRow
                (columns.map fun column ↦
                  (rows.map fun row ↦ weight row * entry row column).sum) =
          (rows.map fun row ↦
            weight row *
              (entry row column +
                gramEncodingBase *
                  encodeGramRow
                    (columns.map fun column ↦ entry row column))).sum
      rw [ih]
      simp only [mul_add]
      rw [List.sum_map_add]
      congr 1
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro row hrow
      ring

private theorem map_getD_range (entries : List α) (fallback : α) :
    (List.range entries.length).map (fun i ↦ entries.getD i fallback) =
      entries := by
  apply List.ext_getElem
  · simp
  · intro i hi hentries
    simp only [List.getElem_map]
    have hrange :
        (List.range entries.length)[i]'(by simpa using hentries) = i := by
      simp
    rw [hrange]
    rw [List.getD_eq_getElem _ _ hentries]

private theorem fixedIntRow_eq_map_getD
    (n : Nat) (entries : List Int) :
    fixedIntRow n entries =
      (List.range n).map fun i ↦ entries.getD i 0 := by
  induction n generalizing entries with
  | zero =>
      simp [fixedIntRow]
  | succ n ih =>
      rw [List.range_succ_eq_map]
      cases entries with
      | nil =>
          simp [fixedIntRow, ih, Function.comp_def]
      | cons entry entries =>
          simp [fixedIntRow, ih, Function.comp_def]

private theorem factorCoefficientRow_eq_map (r : Nat)
    (hrow : factorRow r = factorData.getD r []) :
    factorCoefficientRow r =
      (List.range 425).map fun i ↦
        fullFactorCoefficient (factorData.getD r []) i := by
  dsimp only [factorCoefficientRow, factorCoefficientRowOf]
  rw [hrow]
  rw [show 425 = 424 + 1 by omega, List.range_succ_eq_map]
  rw [fixedIntRow_eq_map_getD]
  simp [fullFactorCoefficient, Function.comp_def]

private theorem fullGramCoefficientRow_eq_map (i : Nat) :
    fullGramCoefficientRow i =
      (List.range 425).map fun j ↦ fullGramCoefficient i j := by
  unfold fullGramCoefficientRow fullGramCoefficient
  rw [fixedIntRow_eq_map_getD]

private theorem encodedFullGramColumnCombinationAux_eq
    (n : Nat) (coefficients : List Int)
    (encodings : List Int) (result : Int) :
    encodedFullGramColumnCombinationAux n coefficients encodings result =
      result +
        ((List.range n).map fun r ↦
          coefficients.getD r 0 * encodings.getD r 0).sum := by
  induction n generalizing coefficients encodings result with
  | zero =>
      simp [encodedFullGramColumnCombinationAux]
  | succ n ih =>
      rw [List.range_succ_eq_map]
      cases coefficients <;> cases encodings <;>
        simp [encodedFullGramColumnCombinationAux, ih,
          Function.comp_def, add_assoc]

private theorem encodedFullGramColumnCombination_eq_range
    (columnChecks :
      ∀ chunk : Fin 14, factorColumnChunkIsValid chunk = true)
    (i : Fin 425) :
    encodedFullGramColumnCombination i =
      ((List.range 424).map fun r ↦
        fullFactorCoefficient (factorData.getD r []) i *
          encodedFactorRows.getD r 0).sum := by
  unfold encodedFullGramColumnCombination
  rw [encodedFullGramColumnCombinationAux_eq]
  simp only [zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  exact
    factorColumn_getD_eq_of_chunk_checks columnChecks i
      ⟨r, List.mem_range.mp hr⟩

private theorem abs_list_sum_le_length_mul
    (entries : List ℤ) (bound : ℤ)
    (hbound : ∀ entry ∈ entries, |entry| ≤ bound) :
    |entries.sum| ≤ entries.length * bound := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      calc
        |(entry :: entries).sum| =
            |entry + entries.sum| := by rfl
        _ ≤ |entry| + |entries.sum| := abs_add_le entry entries.sum
        _ ≤ bound + entries.length * bound :=
          add_le_add (hbound entry (by simp)) (ih (by
            intro x hx
            exact hbound x (by simp [hx])))
        _ = (entry :: entries).length * bound := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

private def calculatedFullGramCoefficient (i j : ℕ) : ℤ :=
  ((List.range 424).map fun r ↦
    fullFactorCoefficient (factorData.getD r []) i *
      fullFactorCoefficient (factorData.getD r []) j).sum

private def calculatedFullGramRow (i : ℕ) : List ℤ :=
  (List.range 425).map fun j ↦ calculatedFullGramCoefficient i j

private theorem factorRowEncoding_eq
    (factorChecks :
      ∀ r : Fin 424, factorRowEncodingIsValid r = true)
    (r : Fin 424) :
    encodedFactorRows.getD r 0 =
      encodeGramRow (factorCoefficientRow r) := by
  have h := factorChecks r
  simp only [factorRowEncodingIsValid, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

private theorem factorCoefficient_abs_le
    (factorChecks :
      ∀ r : Fin 424, factorRowEncodingIsValid r = true)
    (r : Fin 424) (i : Fin 425) :
    |fullFactorCoefficient (factorData.getD r []) i| ≤
      factorCoefficientBound := by
  have h := factorChecks r
  simp only [factorRowEncodingIsValid, Bool.and_eq_true] at h
  have hmember :
      fullFactorCoefficient (factorData.getD r []) i ∈
        factorCoefficientRow r := by
    rw [factorCoefficientRow_eq_map r
      (factorRow_eq_factorData_getD r)]
    exact List.mem_map.mpr
      ⟨i, List.mem_range.mpr i.isLt, rfl⟩
  have hi := List.all_eq_true.mp h.2 _ hmember
  exact abs_le.mpr (of_decide_eq_true hi)

private theorem fullGramRowEncoding_eq
    (gramChecks :
      ∀ i : Fin 425, fullGramRowEncodingIsValid i = true)
    (i : Fin 425) :
    encodeGramRow (fullGramCoefficientRow i) =
      encodedFullGramColumnCombination i := by
  have h := gramChecks i
  simp only [fullGramRowEncodingIsValid, Bool.and_eq_true] at h
  unfold fullGramCoefficientRow
  rw [coefficientFullGramData_getD]
  exact of_decide_eq_true h.2.1

private theorem fullGramCoefficient_abs_le
    (gramChecks :
      ∀ i : Fin 425, fullGramRowEncodingIsValid i = true)
    (i j : Fin 425) :
    |fullGramCoefficient i j| ≤ fullGramCoefficientBound := by
  have h := gramChecks i
  simp only [fullGramRowEncodingIsValid, Bool.and_eq_true] at h
  have hmember :
      fullGramCoefficient i j ∈ fullGramCoefficientRow i := by
    rw [fullGramCoefficientRow_eq_map]
    exact List.mem_map.mpr
      ⟨j, List.mem_range.mpr j.isLt, rfl⟩
  unfold fullGramCoefficientRow at hmember
  rw [coefficientFullGramData_getD] at hmember
  have hj := List.all_eq_true.mp h.2.2 _ hmember
  exact abs_le.mpr (of_decide_eq_true hj)



theorem fullGramDataRow_length_of_encoding_checks
    (gramChecks :
      ∀ i : Fin 425, fullGramRowEncodingIsValid i = true)
    (i : Fin 425) :
    (fullGramData.getD i []).length = 425 := by
  have hi := gramChecks i
  simp only [fullGramRowEncodingIsValid, Bool.and_eq_true] at hi
  rw [coefficientFullGramData_getD]
  exact of_decide_eq_true hi.1

private theorem calculatedFullGramCoefficient_abs_le
    (factorChecks :
      ∀ r : Fin 424, factorRowEncodingIsValid r = true)
    (i j : Fin 425) :
    |calculatedFullGramCoefficient i j| ≤
      424 * factorCoefficientBound ^ 2 := by
  unfold calculatedFullGramCoefficient
  apply abs_list_sum_le_length_mul
  intro entry hentry
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hentry
  have hrlt : r < 424 := List.mem_range.mp hr
  rw [abs_mul]
  rw [pow_two]
  apply mul_le_mul
  · exact factorCoefficient_abs_le factorChecks ⟨r, hrlt⟩ i
  · exact factorCoefficient_abs_le factorChecks ⟨r, hrlt⟩ j
  · exact abs_nonneg _
  · norm_num [factorCoefficientBound]

private theorem fullGramRow_eq_calculated
    (columnChecks :
      ∀ chunk : Fin 14, factorColumnChunkIsValid chunk = true)
    (factorChecks :
      ∀ r : Fin 424, factorRowEncodingIsValid r = true)
    (gramChecks :
      ∀ i : Fin 425, fullGramRowEncodingIsValid i = true)
    (i : Fin 425) :
    fullGramCoefficientRow i = calculatedFullGramRow i := by
  apply encodeGramRow_injective_of_difference_bound
  · have hbounds (indices : List ℕ)
        (hindices : ∀ j ∈ indices, j < 425) :
        List.Forall₂
          (fun x y ↦
            -gramEncodingBase < x - y ∧ x - y < gramEncodingBase)
          (indices.map fun j ↦ fullGramCoefficient i j)
          (indices.map fun j ↦ calculatedFullGramCoefficient i j) := by
      induction indices with
      | nil => exact .nil
      | cons j indices ih =>
          apply List.Forall₂.cons
          · have hj : j < 425 := hindices j (by simp)
            have hstored :
                |fullGramCoefficient i j| ≤
                  fullGramCoefficientBound := by
              simpa using
                (fullGramCoefficient_abs_le gramChecks i ⟨j, hj⟩)
            have hcalculated :
                |calculatedFullGramCoefficient i j| ≤
                  424 * factorCoefficientBound ^ 2 := by
              simpa using
                (calculatedFullGramCoefficient_abs_le
                  factorChecks i ⟨j, hj⟩)
            rw [abs_le] at hstored hcalculated
            change
              -gramEncodingBase <
                    fullGramCoefficient i j -
                      calculatedFullGramCoefficient i j ∧
                fullGramCoefficient i j -
                    calculatedFullGramCoefficient i j <
                  gramEncodingBase
            unfold gramEncodingBase fullGramCoefficientBound
              factorCoefficientBound at *
            constructor <;> omega
          · exact ih (by
              intro k hk
              exact hindices k (by simp [hk]))
    rw [fullGramCoefficientRow_eq_map]
    unfold calculatedFullGramRow
    exact hbounds (List.range 425) (by simp)
  · calc
      encodeGramRow (fullGramCoefficientRow i) =
          encodedFullGramColumnCombination i :=
        fullGramRowEncoding_eq gramChecks i
      _ = ((List.range 424).map fun r ↦
            fullFactorCoefficient (factorData.getD r []) i *
              encodedFactorRows.getD r 0).sum :=
        encodedFullGramColumnCombination_eq_range columnChecks i
      _ = ((List.range 424).map fun r ↦
            fullFactorCoefficient (factorData.getD r []) i *
              encodeGramRow (factorCoefficientRow r)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro r hr
        congr 1
        exact factorRowEncoding_eq factorChecks
          ⟨r, List.mem_range.mp hr⟩
      _ = encodeGramRow (calculatedFullGramRow i) := by
        calc
          ((List.range 424).map fun r ↦
              fullFactorCoefficient (factorData.getD r []) i *
                encodeGramRow (factorCoefficientRow r)).sum =
              ((List.range 424).map fun r ↦
                fullFactorCoefficient (factorData.getD r []) i *
                  encodeGramRow
                    ((List.range 425).map fun j ↦
                      fullFactorCoefficient (factorData.getD r []) j)).sum := by
                apply congrArg List.sum
                apply List.map_congr_left
                intro r hr
                rw [factorCoefficientRow_eq_map r
                  (factorRow_eq_factorData_getD
                    ⟨r, List.mem_range.mp hr⟩)]
          _ = encodeGramRow (calculatedFullGramRow i) := by
                unfold calculatedFullGramRow calculatedFullGramCoefficient
                exact
                    (encodeGramRow_weighted_sum
                    (List.range 424) (List.range 425)
                    (fun r ↦
                      fullFactorCoefficient (factorData.getD r []) i)
                    (fun r j ↦
                      fullFactorCoefficient (factorData.getD r []) j)).symm

theorem fullGram_valid_of_encoding_checks
    (factorDataLength : factorData.length = 424)
    (columnChecks :
      ∀ chunk : Fin 14, factorColumnChunkIsValid chunk = true)
    (factorChecks :
      ∀ r : Fin 424, factorRowEncodingIsValid r = true)
    (gramChecks :
      ∀ i : Fin 425, fullGramRowEncodingIsValid i = true) :
    ∀ i j : Fin 425,
      fullGramCoefficient i j =
        (factorData.map fun row ↦
          fullFactorCoefficient row i *
            fullFactorCoefficient row j).sum := by
  intro i j
  have hrows :=
    fullGramRow_eq_calculated columnChecks factorChecks gramChecks i
  have hcoefficient :=
    congrArg (fun row : List ℤ ↦ row.getD j 0) hrows
  have hcalculated :
      fullGramCoefficient i j =
        calculatedFullGramCoefficient i j := by
    rw [fullGramCoefficientRow_eq_map] at hcoefficient
    simpa [calculatedFullGramRow] using hcoefficient
  rw [hcalculated]
  unfold calculatedFullGramCoefficient
  have hfactorData :
      (List.range 424).map (fun r ↦ factorData.getD r []) =
        factorData := by
    rw [← factorDataLength]
    exact map_getD_range factorData []
  calc
    ((List.range 424).map fun r ↦
        fullFactorCoefficient (factorData.getD r []) i *
          fullFactorCoefficient (factorData.getD r []) j).sum =
        (((List.range 424).map fun r ↦ factorData.getD r []).map
          fun row ↦ fullFactorCoefficient row i *
            fullFactorCoefficient row j).sum := by
          rw [List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r hr
          rfl
    _ = _ := by rw [hfactorData]

end

end AffineSymplecticCertificate

end ConnesRigidity

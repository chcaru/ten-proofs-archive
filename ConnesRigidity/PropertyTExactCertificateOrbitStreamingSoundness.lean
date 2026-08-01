


import ConnesRigidity.PropertyTExactCertificateOrbitCheckerValidation









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



theorem orbitConsumeCoefficientTerms_sound
    (key : Int) (count : Nat) (rows : List (Array Int))
    (initial total : Int) (remaining : List (Array Int))
    (h : orbitConsumeCoefficientTerms key count rows initial =
      some (total, remaining)) :
    count ≤ rows.length ∧ remaining = rows.drop count ∧
      (∀ row ∈ rows.take count,
        row.size = coefficientTermRowWidth ∧ orbitEntry row 0 = key) ∧
      total = initial + ((rows.take count).map orbitCoefficientTermValue).sum := by
  induction count generalizing rows initial with
  | zero =>
      simp only [orbitConsumeCoefficientTerms] at h
      cases h
      simp
  | succ count ih =>
      cases rows with
      | nil => simp [orbitConsumeCoefficientTerms] at h
      | cons row rows =>
          simp only [orbitConsumeCoefficientTerms] at h
          split at h
          next hrow =>
            obtain ⟨hlen, hremaining, hrows, htotal⟩ :=
              ih rows (initial + orbitCoefficientTermValue row) h
            refine ⟨Nat.succ_le_succ hlen, ?_, ?_, ?_⟩
            · simpa using hremaining
            · intro candidate hcandidate
              simp only [List.take_succ_cons, List.mem_cons] at hcandidate
              rcases hcandidate with rfl | hcandidate
              · exact hrow
              · exact hrows candidate hcandidate
            · simpa [Int.add_assoc] using htotal
          next hrow => simp at h


theorem orbitArrayFoldl_slice {α β : Type}
    (data : Array α) (step : β → α → β) (initial : β)
    (start count : Nat) :
    data.foldl step initial start (start + count) =
      ((data.toList.drop start).take count).foldl step initial := by
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList,
    Array.toList_extract, List.extract_eq_take_drop]
  simp

private theorem orbitListFoldAnd_eq_all {α : Type}
    (rows : List α) (predicate : α → Bool) (initial : Bool) :
    rows.foldl (fun valid row => valid && predicate row) initial =
      (initial && rows.all predicate) := by
  induction rows generalizing initial with
  | nil => simp
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      simp [Bool.and_assoc]



theorem orbitCoefficientRangeTermsCheck_eq_all
    (start count : Nat) (key : Int) :
    orbitCoefficientRangeTermsCheck start count key =
      ((coefficientTermData.toList.drop start).take count).all
        (fun row =>
          decide (row.size = coefficientTermRowWidth) &&
            decide (orbitEntry row 0 = key)) := by
  unfold orbitCoefficientRangeTermsCheck
  rw [orbitArrayFoldl_slice]
  simpa only [Bool.and_assoc, Bool.true_and] using
    orbitListFoldAnd_eq_all
      ((coefficientTermData.toList.drop start).take count)
      (fun row =>
        decide (row.size = coefficientTermRowWidth) &&
          decide (orbitEntry row 0 = key))
      true


theorem orbitCoefficientRangeTotal_eq_sum (start count : Nat) :
    orbitCoefficientRangeTotal start count =
      (((coefficientTermData.toList.drop start).take count).map
        orbitCoefficientTermValue).sum := by
  unfold orbitCoefficientRangeTotal
  rw [orbitArrayFoldl_slice, ← List.foldl_map, ← List.sum_eq_foldl]





theorem orbitCoefficientStreamingCheck_sound
    (equations terms : List (Array Int)) (position : Nat)
    (hterms : terms = coefficientTermData.toList.drop position)
    (hposition : position ≤ coefficientTermData.size)
    (hcheck : orbitCoefficientStreamingCheck equations terms position = true) :
    ∀ row ∈ equations,
      row.size = coefficientEquationRowWidth ∧
        0 ≤ orbitEntry row 1 ∧
        0 ≤ orbitEntry row 2 ∧
        (orbitEntry row 1).toNat + (orbitEntry row 2).toNat ≤
          coefficientTermData.size ∧
        orbitCoefficientRangeTermsCheck
          (orbitEntry row 1).toNat (orbitEntry row 2).toNat
            (orbitEntry row 0) = true ∧
        orbitCoefficientRangeTotal
          (orbitEntry row 1).toNat (orbitEntry row 2).toNat =
            orbitEntry row 3 := by
  induction equations generalizing terms position with
  | nil => simp
  | cons row equations ih =>
      simp only [orbitCoefficientStreamingCheck] at hcheck
      split at hcheck
      next hschema =>
        cases hconsume : orbitConsumeCoefficientTerms
            (orbitEntry row 0) (orbitEntry row 2).toNat terms 0 with
        | none => simp [hconsume] at hcheck
        | some pair =>
          obtain ⟨total, remaining⟩ := pair
          simp only [hconsume, Bool.and_eq_true, decide_eq_true_eq] at hcheck
          obtain ⟨htarget, hrest⟩ := hcheck
          obtain ⟨hcount, hremaining, hrows, htotal⟩ :=
            orbitConsumeCoefficientTerms_sound
              (orbitEntry row 0) (orbitEntry row 2).toNat terms
              0 total remaining hconsume
          obtain ⟨hwidth, hstart, hnonneg⟩ := hschema
          have hstartnat : (orbitEntry row 1).toNat = position := by
            simp [hstart]
          have hcountbound :
              position + (orbitEntry row 2).toNat ≤ coefficientTermData.size := by
            have hlength : terms.length = coefficientTermData.size - position := by
              rw [hterms, List.length_drop, Array.length_toList]
            rw [hlength] at hcount
            omega
          have hremainingTerms :
              remaining = coefficientTermData.toList.drop
                (position + (orbitEntry row 2).toNat) := by
            rw [hremaining, hterms, List.drop_drop]
          intro candidate hcandidate
          simp only [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hcandidate
          · refine ⟨hwidth, ?_, hnonneg, ?_, ?_, ?_⟩
            · rw [hstart]
              exact Int.natCast_nonneg position
            · simpa [hstartnat] using hcountbound
            · rw [orbitCoefficientRangeTermsCheck_eq_all, hstartnat,
                  ← hterms, List.all_eq_true]
              intro term hterm
              simpa only [Bool.and_eq_true, decide_eq_true_eq] using
                hrows term hterm
            · rw [orbitCoefficientRangeTotal_eq_sum, hstartnat, ← hterms]
              simpa using htotal.symm.trans htarget
          · exact ih remaining
              (position + (orbitEntry row 2).toNat)
              hremainingTerms hcountbound hrest candidate hcandidate
      next hschema => simp at hcheck



theorem orbitCoefficientCheck_valid : orbitCoefficientCheck = true := by
  unfold orbitCoefficientCheck
  rw [List.all_eq_true]
  intro index hindex
  have hindex' : index < coefficientEquationData.size := by
    simpa using hindex
  let row := coefficientEquationData[index]'hindex'
  have hrow : coefficientEquationData[index]? = some row :=
    Array.getElem?_eq_getElem hindex'
  have hmember : row ∈ coefficientEquationData.toList :=
    Array.getElem_mem_toList hindex'
  have hsemantic := orbitCoefficientStreamingCheck_sound
    coefficientEquationData.toList coefficientTermData.toList 0
    (by simp) (Nat.zero_le _)
    orbitCoefficientStreamingCheck_valid row hmember
  simpa only [orbitCoefficientRowCheck, hrow, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] using hsemantic

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

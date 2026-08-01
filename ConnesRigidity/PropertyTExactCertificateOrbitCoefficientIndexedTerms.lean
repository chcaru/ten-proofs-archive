


import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCheckerSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitStreamingSoundness













namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section


private theorem coefficient_fold_key_eq_filter_sum
    {α : Type*} (rows : List α)
    (key : α → Int) (value : α → Int)
    (requested : Int) (initial : Int) :
    rows.foldl
        (fun total row =>
          if key row = requested then total + value row else total)
        initial =
      initial +
        ((rows.filter fun row => key row = requested).map value).sum := by
  induction rows generalizing initial with
  | nil => simp
  | cons row rows ih =>
      by_cases hrow : key row = requested
      · simp [hrow, ih, Int.add_assoc]
      · simp [hrow, ih]



private theorem coefficient_filter_eq_slice_of_partition
    {α : Type*} (rows : List α)
    (predicate : α → Bool) (start count : Nat)
    (hprefix : ∀ row ∈ rows.take start, predicate row = false)
    (hslice : ∀ row ∈ (rows.drop start).take count,
      predicate row = true)
    (hsuffix : ∀ row ∈ rows.drop (start + count),
      predicate row = false) :
    rows.filter predicate = (rows.drop start).take count := by
  have filter_eq_nil (values : List α)
      (hvalues : ∀ value ∈ values, predicate value = false) :
      values.filter predicate = [] := by
    induction values with
    | nil => rfl
    | cons value values ih =>
        simp [hvalues value (by simp),
          ih (fun other hother => hvalues other (by simp [hother]))]
  have filter_eq_self (values : List α)
      (hvalues : ∀ value ∈ values, predicate value = true) :
      values.filter predicate = values := by
    induction values with
    | nil => rfl
    | cons value values ih =>
        simp [hvalues value (by simp),
          ih (fun other hother => hvalues other (by simp [hother]))]
  have hdecomposition :
      rows = rows.take start ++
        (rows.drop start).take count ++
        rows.drop (start + count) := by
    calc
      rows = rows.take start ++ rows.drop start :=
        (List.take_append_drop start rows).symm
      _ = rows.take start ++
            ((rows.drop start).take count ++
              (rows.drop start).drop count) := by
                exact congrArg (List.append (rows.take start))
                  (List.take_append_drop count (rows.drop start)).symm
      _ = _ := by
        simp [List.drop_drop, List.append_assoc]
  calc
    rows.filter predicate =
        (rows.take start ++ (rows.drop start).take count ++
          rows.drop (start + count)).filter predicate :=
      congrArg (List.filter predicate) hdecomposition
    _ = _ := by
      rw [List.filter_append, List.filter_append,
        filter_eq_nil _ hprefix,
        filter_eq_self _ hslice,
        filter_eq_nil _ hsuffix]
      simp



theorem orbitCoefficientTerm_equation_slice
    (index : Nat) (hindex : index < coefficientTermData.size) :
    let term := coefficientTermData[index]'hindex
    let equation := dataEntry coefficientOrbitEquationIndexData
      (orbitEntry term 0).toNat 0
    0 ≤ equation ∧ equation < (coefficientEquationData.size : Int) ∧
      coefficientEquationOrbit equation.toNat = orbitEntry term 0 ∧
      (coefficientEquationStart equation.toNat).toNat ≤ index ∧
      index < (coefficientEquationStart equation.toNat).toNat +
        (coefficientEquationCount equation.toNat).toNat := by
  have hwitnessIndex : index < coefficientTermGramOrbitIndexData.size := by
    rwa [coefficientTermGramOrbitIndexData_size]
  let term := coefficientTermData[index]'hindex
  let witness := coefficientTermGramOrbitIndexData[index]'hwitnessIndex
  have hterm : coefficientTermData[index]? = some term :=
    Array.getElem?_eq_getElem hindex
  have hwitness : coefficientTermGramOrbitIndexData[index]? = some witness :=
    Array.getElem?_eq_getElem hwitnessIndex
  have hcheck := orbitCoefficientTermGramOrbitRowCheck_valid index hindex
  simp only [orbitCoefficientTermGramOrbitRowCheck, hterm, hwitness,
    orbitIndexCheck, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hcheck
  obtain ⟨_htermWidth, _hwitnessWidth, _horbitNonneg, _horbitLt,
    hequationNonneg, hequationLt, _hgramKey, _hgramIncidence,
    _hgramValue, _hgramNonzero, hequationKey, hstart, hend,
    _hreverse⟩ := hcheck
  refine ⟨hequationNonneg, hequationLt, ?_, ?_, ?_⟩
  · simpa [coefficientEquationOrbit, dataEntry, orbitEntry] using
      hequationKey
  · simpa [coefficientEquationStart, dataEntry, orbitEntry] using hstart
  · simpa [coefficientEquationStart, coefficientEquationCount,
      dataEntry, orbitEntry] using hend



theorem orbitCoefficientTerm_mem_inverse_slice
    (key : Int) (equation : Nat)
    (hinverse : dataEntry coefficientOrbitEquationIndexData key.toNat 0 =
      (equation : Int))
    (index : Nat) (hindex : index < coefficientTermData.size)
    (hkey : orbitEntry (coefficientTermData[index]'hindex) 0 = key) :
    (coefficientEquationStart equation).toNat ≤ index ∧
      index < (coefficientEquationStart equation).toNat +
        (coefficientEquationCount equation).toNat := by
  have hslice := orbitCoefficientTerm_equation_slice index hindex
  simp only [hkey, hinverse, Int.toNat_natCast] at hslice
  exact hslice.2.2.2



private theorem coefficient_equation_get_field
    (equation : Nat) (hequation : equation < coefficientEquationData.size)
    (column : Nat) :
    orbitEntry (coefficientEquationData[equation]'hequation) column =
      dataEntry coefficientEquationData equation column := by
  simp [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?, hequation]



theorem orbitCoefficientTotal_eq_active_equation
    (key : Int) (equation : Nat)
    (hequation : equation < coefficientEquationData.size)
    (hinverse : dataEntry coefficientOrbitEquationIndexData key.toNat 0 =
      (equation : Int))
    (hkey : coefficientEquationOrbit equation = key) :
    orbitCoefficientTotal key = coefficientEquationTarget equation := by
  let rows := coefficientTermData.toList
  let start := (coefficientEquationStart equation).toNat
  let count := (coefficientEquationCount equation).toNat
  let equationRow := coefficientEquationData[equation]'hequation
  have hequationRow : coefficientEquationData[equation]? =
      some equationRow := Array.getElem?_eq_getElem hequation
  have hvalid := (orbitCoefficientCheck_sound orbitCoefficientCheck_valid)
    equation hequation
  have hsemantic := orbitCoefficientRowCheck_sound equation equationRow
    hequationRow hvalid
  have hrowkey : orbitEntry equationRow 0 = key := by
    rw [coefficient_equation_get_field equation hequation 0]
    exact hkey
  have hrowstart : (orbitEntry equationRow 1).toNat = start := by
    change (orbitEntry equationRow 1).toNat =
      (dataEntry coefficientEquationData equation 1).toNat
    exact congrArg Int.toNat
      (coefficient_equation_get_field equation hequation 1)
  have hrowcount : (orbitEntry equationRow 2).toNat = count := by
    change (orbitEntry equationRow 2).toNat =
      (dataEntry coefficientEquationData equation 2).toNat
    exact congrArg Int.toNat
      (coefficient_equation_get_field equation hequation 2)
  have hrowtarget : orbitEntry equationRow 3 =
      coefficientEquationTarget equation := by
    exact coefficient_equation_get_field equation hequation 3
  have hslice : ∀ row ∈ (rows.drop start).take count,
      decide (orbitEntry row 0 = key) = true := by
    intro row hrow
    have hterms := hsemantic.2.2.2.2.1
    rw [orbitCoefficientRangeTermsCheck_eq_all, hrowstart, hrowcount,
      hrowkey, List.all_eq_true] at hterms
    have hterm := hterms row hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hterm
    exact decide_eq_true_eq.mpr hterm.2
  have hprefix : ∀ row ∈ rows.take start,
      decide (orbitEntry row 0 = key) = false := by
    intro row hrow
    simp only [decide_eq_false_iff_not]
    intro hkeyrow
    obtain ⟨index, hindex, hget⟩ :=
      List.mem_take_iff_getElem.mp hrow
    have hlt : index < coefficientTermData.size := by
      have := (Nat.lt_min.mp hindex).2
      simpa [rows] using this
    have hterm : coefficientTermData[index]'hlt = row := by
      simpa [rows] using hget
    have htermkey : orbitEntry (coefficientTermData[index]'hlt) 0 = key := by
      simpa [hterm] using hkeyrow
    have hbound := orbitCoefficientTerm_mem_inverse_slice
      key equation hinverse index hlt htermkey
    have hbefore := (Nat.lt_min.mp hindex).1
    omega
  have hsuffix : ∀ row ∈ rows.drop (start + count),
      decide (orbitEntry row 0 = key) = false := by
    intro row hrow
    simp only [decide_eq_false_iff_not]
    intro hkeyrow
    obtain ⟨offset, hoffset, hget⟩ :=
      List.mem_drop_iff_getElem.mp hrow
    have hlt : start + count + offset < coefficientTermData.size := by
      simpa [rows, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hoffset
    have hterm :
        coefficientTermData[start + count + offset]'hlt = row := by
      simpa [rows] using hget
    have htermkey :
        orbitEntry (coefficientTermData[start + count + offset]'hlt) 0 =
          key := by
      simpa [hterm] using hkeyrow
    have hbound := orbitCoefficientTerm_mem_inverse_slice
      key equation hinverse (start + count + offset) hlt htermkey
    have hout := hbound.2
    change start + count + offset < start + count at hout
    omega
  have hfilter := coefficient_filter_eq_slice_of_partition rows
    (fun row => decide (orbitEntry row 0 = key)) start count
    hprefix hslice hsuffix
  unfold orbitCoefficientTotal
  rw [coefficient_fold_key_eq_filter_sum]
  simp only [zero_add]
  rw [hfilter, ← orbitCoefficientRangeTotal_eq_sum]
  rw [← hrowstart, ← hrowcount]
  exact hsemantic.2.2.2.2.2.trans hrowtarget



theorem orbitCoefficientTotal_eq_zero_of_inactive
    (key : Int)
    (hinactive : dataEntry coefficientOrbitEquationIndexData key.toNat 0 =
      -1) :
    orbitCoefficientTotal key = 0 := by
  let rows := coefficientTermData.toList
  have hnomatch : ∀ row ∈ rows, orbitEntry row 0 ≠ key := by
    intro row hrow hkey
    obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hrow
    have hindex' : index < coefficientTermData.size := by
      simpa [rows] using hindex
    have hterm : coefficientTermData[index]'hindex' = row := by
      simpa [rows] using hget
    have hkey' : orbitEntry (coefficientTermData[index]'hindex') 0 =
        key := by
      simpa [hterm] using hkey
    have hnonnegative :=
      (orbitCoefficientTerm_equation_slice index hindex').1
    simp only [hkey', hinactive] at hnonnegative
    omega
  have hfilter :
      rows.filter (fun row => orbitEntry row 0 = key) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row hrow hselected
    exact hnomatch row hrow (of_decide_eq_true hselected)
  unfold orbitCoefficientTotal
  rw [coefficient_fold_key_eq_filter_sum]
  simp only [zero_add]
  change ((rows.filter (fun row => orbitEntry row 0 = key)).map
    orbitCoefficientTermValue).sum = 0
  simp [hfilter]



theorem orbitCoefficientTotal_eq_target
    (coefficient : Fin 995) :
    orbitCoefficientTotal (coefficient.val : Int) =
      coefficientOrbitTarget coefficient.val := by
  have hcoefficient : coefficient.val < coefficientRepresentativeData.size := by
    simp [coefficientRepresentativeData_size]
  have hinverseIndex : coefficient.val <
      coefficientOrbitEquationIndexData.size := by
    rw [coefficientOrbitEquationIndexData_size]
    exact hcoefficient
  have htargetIndex : coefficient.val < coefficientTargetData.size := by
    rw [coefficientTargetData_size]
    exact hcoefficient
  let inverse := coefficientOrbitEquationIndexData[coefficient.val]'hinverseIndex
  let target := coefficientTargetData[coefficient.val]'htargetIndex
  have hinverseRow : coefficientOrbitEquationIndexData[coefficient.val]? =
      some inverse := Array.getElem?_eq_getElem hinverseIndex
  have htargetRow : coefficientTargetData[coefficient.val]? =
      some target := Array.getElem?_eq_getElem htargetIndex
  have hinverseEntry :
      dataEntry coefficientOrbitEquationIndexData coefficient.val 0 =
        orbitEntry inverse 0 := by
    simp [inverse, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hinverseIndex]
  have htargetEntry :
      coefficientOrbitTarget coefficient.val = orbitEntry target 0 := by
    simp [coefficientOrbitTarget, target, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, htargetIndex]
  have hcheck := orbitCoefficientOrbitEquationRowCheck_valid
    coefficient.val hcoefficient
  simp only [orbitCoefficientOrbitEquationRowCheck, hinverseRow, htargetRow,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hcheck
  by_cases hinactive : orbitEntry inverse 0 = -1
  · have hzero : orbitEntry target 0 = 0 := by
      simpa [hinactive] using hcheck.2.2
    rw [orbitCoefficientTotal_eq_zero_of_inactive
      (coefficient.val : Int)]
    · rw [htargetEntry, hzero]
    · simpa [hinverseEntry] using hinactive
  · have hactive := hcheck.2.2
    simp only [hinactive, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, orbitIndexCheck] at hactive
    obtain ⟨⟨⟨hnonnegative, hbound⟩, hkey⟩, htargetValue⟩ := hactive
    let equation := (orbitEntry inverse 0).toNat
    have hequation : equation < coefficientEquationData.size :=
      (Int.toNat_lt hnonnegative).mpr hbound
    have hinverse :
        dataEntry coefficientOrbitEquationIndexData
            (coefficient.val : Int).toNat 0 = (equation : Int) := by
      simp only [Int.toNat_natCast, hinverseEntry, equation]
      exact (Int.toNat_of_nonneg hnonnegative).symm
    rw [orbitCoefficientTotal_eq_active_equation
      (coefficient.val : Int) equation hequation hinverse hkey]
    exact htargetValue.trans htargetEntry.symm

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

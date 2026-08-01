


import ConnesRigidity.PropertyTExactCertificateOrbitCheckerSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientIndexedTerms
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
import ConnesRigidity.PropertyTExactCertificateOrbitStreamingSoundness











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

set_option maxRecDepth 1000000





theorem sum_sparse_orbit_terms_of_inverse
    {gramCount termCount : Nat}
    (gramKey gramIncidence gramValue : Fin gramCount → Int)
    (termKey termIncidence termValue : Fin termCount → Int)
    (termOrbit : Fin termCount → Fin gramCount)
    (inverse : Fin gramCount → Option (Fin termCount))
    (hinverse : ∀ term, inverse (termOrbit term) = some term)
    (hcomplete : ∀ orbit, gramValue orbit ≠ 0 →
      ∃ term, termOrbit term = orbit)
    (hterm_nonzero : ∀ term, termValue term ≠ 0)
    (hkey : ∀ term, termKey term = gramKey (termOrbit term))
    (hincidence : ∀ term,
      termIncidence term = gramIncidence (termOrbit term))
    (hvalue : ∀ term, termValue term = gramValue (termOrbit term))
    (key : Int) :
    (∑ orbit : Fin gramCount,
      if gramKey orbit = key
      then gramIncidence orbit * gramValue orbit
      else 0) =
    ∑ term : Fin termCount,
      if termKey term = key
      then termIncidence term * termValue term
      else 0 := by
  classical
  let active : Finset (Fin gramCount) :=
    Finset.univ.filter fun orbit => gramValue orbit ≠ 0
  have hfiltered :
      (∑ orbit : Fin gramCount,
        if gramKey orbit = key
        then gramIncidence orbit * gramValue orbit
        else 0) =
      ∑ orbit ∈ active,
        if gramKey orbit = key
        then gramIncidence orbit * gramValue orbit
        else 0 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro orbit _horbit hnot
    have hzero : gramValue orbit = 0 := by
      simpa [active] using hnot
    simp [hzero]
  rw [hfiltered]
  symm
  apply Finset.sum_bij
    (fun term _hterm => termOrbit term)
  · intro term _hterm
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hvalue term]
    exact hterm_nonzero term
  · intro first _hfirst second _hsecond heq
    have hboth := congrArg inverse heq
    simpa [hinverse] using hboth
  · intro orbit horbit
    have hnonzero : gramValue orbit ≠ 0 :=
      (Finset.mem_filter.mp horbit).2
    obtain ⟨term, hterm⟩ := hcomplete orbit hnonzero
    exact ⟨term, Finset.mem_univ term, hterm⟩
  · intro term _hterm
    rw [hkey term, hincidence term, hvalue term]




theorem orbitCoefficientTermGram_semantics (term : Fin 1798) :
    let orbit := dataEntry coefficientTermGramOrbitIndexData term.val 0
    0 ≤ orbit ∧ orbit < (2256 : Int) ∧
      dataEntry coefficientTermData term.val 0 =
        gramOrbitCoefficientOrbit orbit.toNat ∧
      dataEntry coefficientTermData term.val 1 =
        gramOrbitIncidence orbit.toNat ∧
      dataEntry coefficientTermData term.val 2 =
        gramOrbitCoefficient orbit.toNat ∧
      dataEntry coefficientTermData term.val 2 ≠ 0 ∧
      dataEntry gramOrbitTermIndexData orbit.toNat 0 =
        (term.val : Int) := by
  have htermIndex : term.val < coefficientTermData.size := by
    rw [coefficientTermData_size]
    exact term.isLt
  have hwitnessIndex : term.val < coefficientTermGramOrbitIndexData.size := by
    rw [coefficientTermGramOrbitIndexData_size]
    exact htermIndex
  let row := coefficientTermData[term.val]'htermIndex
  let witness := coefficientTermGramOrbitIndexData[term.val]'hwitnessIndex
  have hrow : coefficientTermData[term.val]? = some row :=
    Array.getElem?_eq_getElem htermIndex
  have hwitness : coefficientTermGramOrbitIndexData[term.val]? = some witness :=
    Array.getElem?_eq_getElem hwitnessIndex
  have hcheck := orbitCoefficientTermGramOrbitRowCheck_valid
    term.val htermIndex
  simp only [orbitCoefficientTermGramOrbitRowCheck, hrow, hwitness,
    orbitIndexCheck, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hcheck
  obtain ⟨_hwidth, _hwitnessWidth, horbitNonneg, horbitLt,
    _hequationNonneg, _hequationLt, hkey, hincidence, hvalue,
    hnonzero, _hequationKey, _hstart, _hend, hinverse⟩ := hcheck
  have horbitData :
      dataEntry coefficientTermGramOrbitIndexData term.val 0 =
        orbitEntry witness 0 := by
    simp [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?,
      hwitnessIndex, witness]
  dsimp
  rw [horbitData]
  refine ⟨horbitNonneg, ?_, ?_, ?_, ?_, ?_, hinverse⟩
  · simpa [gramOrbitData_size] using horbitLt
  · simpa [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?,
      htermIndex, row, gramOrbitCoefficientOrbit] using hkey
  · simpa [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?,
      htermIndex, row, gramOrbitIncidence] using hincidence
  · simpa [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?,
      htermIndex, row, gramOrbitCoefficient] using hvalue
  · simpa [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?,
      htermIndex, row] using hnonzero


noncomputable def orbitCoefficientTermGram (term : Fin 1798) : Fin 2256 :=
  ⟨(dataEntry coefficientTermGramOrbitIndexData term.val 0).toNat, by
    have hsemantic := orbitCoefficientTermGram_semantics term
    exact (Int.toNat_lt hsemantic.1).mpr hsemantic.2.1⟩


theorem orbitCoefficientTermGram_fields (term : Fin 1798) :
    dataEntry coefficientTermData term.val 0 =
        gramOrbitCoefficientOrbit (orbitCoefficientTermGram term).val ∧
      dataEntry coefficientTermData term.val 1 =
        gramOrbitIncidence (orbitCoefficientTermGram term).val ∧
      dataEntry coefficientTermData term.val 2 =
        gramOrbitCoefficient (orbitCoefficientTermGram term).val ∧
      dataEntry coefficientTermData term.val 2 ≠ 0 ∧
      dataEntry gramOrbitTermIndexData
        (orbitCoefficientTermGram term).val 0 = (term.val : Int) := by
  exact (orbitCoefficientTermGram_semantics term).2.2


theorem orbitGramTermInverse_semantics (gram : Fin 2256)
    (hnonzero : gramOrbitCoefficient gram.val ≠ 0) :
    let term := dataEntry gramOrbitTermIndexData gram.val 0
    0 ≤ term ∧ term < (1798 : Int) ∧
      dataEntry coefficientTermGramOrbitIndexData term.toNat 0 =
        (gram.val : Int) := by
  have hgramIndex : gram.val < gramOrbitData.size := by
    rw [gramOrbitData_size]
    exact gram.isLt
  have hwitnessIndex : gram.val < gramOrbitTermIndexData.size := by
    rw [gramOrbitTermIndexData_size]
    exact hgramIndex
  let row := gramOrbitData[gram.val]'hgramIndex
  let witness := gramOrbitTermIndexData[gram.val]'hwitnessIndex
  have hrow : gramOrbitData[gram.val]? = some row :=
    Array.getElem?_eq_getElem hgramIndex
  have hwitness : gramOrbitTermIndexData[gram.val]? = some witness :=
    Array.getElem?_eq_getElem hwitnessIndex
  have hcheck := orbitGramTermIndexRowCheck_valid gram.val hgramIndex
  simp only [orbitGramTermIndexRowCheck, hrow, hwitness,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hvalue : orbitEntry row 4 ≠ 0 := by
    simpa [gramOrbitCoefficient, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hgramIndex, row] using hnonzero
  simp only [hvalue, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq, orbitIndexCheck] at hcheck
  obtain ⟨_hwidth, ⟨hnonneg, hbound⟩, hinverse⟩ := hcheck
  have hwitnessData :
      dataEntry gramOrbitTermIndexData gram.val 0 = orbitEntry witness 0 := by
    simp [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?,
      hwitnessIndex, witness]
  dsimp
  rw [hwitnessData]
  exact ⟨hnonneg, by simpa [coefficientTermData_size] using hbound,
    hinverse⟩



noncomputable def orbitGramTermInverse (gram : Fin 2256) :
    Option (Fin 1798) :=
  if hzero : gramOrbitCoefficient gram.val = 0 then
    none
  else
    some ⟨(dataEntry gramOrbitTermIndexData gram.val 0).toNat, by
      have hsemantic := orbitGramTermInverse_semantics gram hzero
      exact (Int.toNat_lt hsemantic.1).mpr hsemantic.2.1⟩


theorem orbitGramTermInverse_coefficientTermGram (term : Fin 1798) :
    orbitGramTermInverse (orbitCoefficientTermGram term) = some term := by
  have hfields := orbitCoefficientTermGram_fields term
  have hnonzero :
      gramOrbitCoefficient (orbitCoefficientTermGram term).val ≠ 0 := by
    rw [← hfields.2.2.1]
    exact hfields.2.2.2.1
  unfold orbitGramTermInverse
  rw [dif_neg hnonzero]
  congr 1
  apply Fin.ext
  have hindex := hfields.2.2.2.2
  exact_mod_cast congrArg Int.toNat hindex


theorem orbitCoefficientTermGram_surjective_nonzero (gram : Fin 2256)
    (hnonzero : gramOrbitCoefficient gram.val ≠ 0) :
    ∃ term : Fin 1798, orbitCoefficientTermGram term = gram := by
  have hsemantic := orbitGramTermInverse_semantics gram hnonzero
  let term : Fin 1798 :=
    ⟨(dataEntry gramOrbitTermIndexData gram.val 0).toNat,
      (Int.toNat_lt hsemantic.1).mpr hsemantic.2.1⟩
  refine ⟨term, Fin.ext ?_⟩
  change
    (dataEntry coefficientTermGramOrbitIndexData term.val 0).toNat =
      gram.val
  have hinverse := hsemantic.2.2
  simpa [term] using congrArg Int.toNat hinverse


theorem orbitArray_fin_sum_eq_list_sum
    {α β : Type*} [AddCommMonoid β]
    (rows : Array α) (value : α → β) :
    (∑ index : Fin rows.size, value rows[index.val]) =
      (rows.toList.map value).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (by
    simpa using List.ofFn_getElem_eq_map rows.toList value)



theorem orbitList_indicator_sum_eq_filter_sum
    {α : Type*} (rows : List α)
    (key : α → Int) (value : α → Int) (requested : Int) :
    (rows.map fun row =>
      if key row = requested then value row else 0).sum =
      ((rows.filter fun row => key row = requested).map value).sum := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      by_cases hrow : key row = requested <;>
        simp [hrow, ih]


theorem orbitFold_keyed_terms_eq_filter_sum
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



theorem orbitGramIncidence_weighted_int_sum_eq_total (key : Int) :
    (∑ gram : Fin 2256,
      if gramOrbitCoefficientOrbit gram.val = key then
        gramOrbitIncidence gram.val * gramOrbitCoefficient gram.val
      else 0) = orbitCoefficientTotal key := by
  have hsparse := sum_sparse_orbit_terms_of_inverse
    (gramCount := 2256) (termCount := 1798)
    (fun gram : Fin 2256 => gramOrbitCoefficientOrbit gram.val)
    (fun gram : Fin 2256 => gramOrbitIncidence gram.val)
    (fun gram : Fin 2256 => gramOrbitCoefficient gram.val)
    (fun term : Fin 1798 => dataEntry coefficientTermData term.val 0)
    (fun term : Fin 1798 => dataEntry coefficientTermData term.val 1)
    (fun term : Fin 1798 => dataEntry coefficientTermData term.val 2)
    orbitCoefficientTermGram orbitGramTermInverse
    orbitGramTermInverse_coefficientTermGram
    orbitCoefficientTermGram_surjective_nonzero
    (fun term => (orbitCoefficientTermGram_fields term).2.2.2.1)
    (fun term => (orbitCoefficientTermGram_fields term).1)
    (fun term => (orbitCoefficientTermGram_fields term).2.1)
    (fun term => (orbitCoefficientTermGram_fields term).2.2.1)
    key
  rw [hsparse]
  have harray := orbitArray_fin_sum_eq_list_sum coefficientTermData
    (fun row =>
      if orbitEntry row 0 = key then orbitCoefficientTermValue row else 0)
  have hreindex := Fintype.sum_equiv
    (finCongr coefficientTermData_size.symm)
    (fun term : Fin 1798 =>
      if dataEntry coefficientTermData term.val 0 = key then
        dataEntry coefficientTermData term.val 1 *
          dataEntry coefficientTermData term.val 2
      else 0)
    (fun term : Fin coefficientTermData.size =>
      if orbitEntry coefficientTermData[term.val] 0 = key then
        orbitCoefficientTermValue coefficientTermData[term.val]
      else 0)
    (by
      intro term
      simp [dataEntry, orbitEntry, orbitCoefficientTermValue,
        Array.getD_eq_getD_getElem?, coefficientTermData_size])
  have harray' :
      (∑ term : Fin 1798,
        if dataEntry coefficientTermData term.val 0 = key then
          dataEntry coefficientTermData term.val 1 *
            dataEntry coefficientTermData term.val 2
        else 0) =
      (coefficientTermData.toList.map fun row =>
        if orbitEntry row 0 = key then orbitCoefficientTermValue row else 0).sum := by
    exact hreindex.trans harray
  rw [harray', orbitList_indicator_sum_eq_filter_sum]
  symm
  exact (orbitFold_keyed_terms_eq_filter_sum coefficientTermData.toList
    (fun row => orbitEntry row 0) orbitCoefficientTermValue key 0).trans
      (by simp)




theorem orbitGramIncidence_weighted_sum_eq_target (coefficient : Fin 995) :
    (∑ gram : Fin 2256,
      if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int) then
        ((gramOrbitIncidence gram.val).toNat : ℚ) *
          (gramOrbitCoefficient gram.val : ℚ)
      else 0) = (coefficientOrbitTarget coefficient.val : ℚ) := by
  have hsum := orbitGramIncidence_weighted_int_sum_eq_total
    (coefficient.val : Int)
  rw [orbitCoefficientTotal_eq_target coefficient] at hsum
  have hrational := congrArg (fun value : Int => (value : ℚ)) hsum
  push_cast at hrational
  have hincidence (gram : Fin 2256) :
      0 ≤ gramOrbitIncidence gram.val := by
    have hindex : gram.val < gramOrbitData.size := by
      rw [gramOrbitData_size]
      exact gram.isLt
    have hfields := orbitGramRepresentativeFields_valid gram.val hindex
    simpa [gramOrbitIncidence, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hindex] using hfields.2.2.2.2.1
  calc
    (∑ gram : Fin 2256,
      if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int) then
        ((gramOrbitIncidence gram.val).toNat : ℚ) *
          (gramOrbitCoefficient gram.val : ℚ)
      else 0) =
      ∑ gram : Fin 2256,
        if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int) then
          (gramOrbitIncidence gram.val : ℚ) *
            (gramOrbitCoefficient gram.val : ℚ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro gram _hgram
          split_ifs
          · congr 1
            exact_mod_cast Int.toNat_of_nonneg (hincidence gram)
          · rfl
    _ = _ := by
      simpa only [Int.cast_ite, Int.cast_zero, Int.cast_mul] using hrational



theorem fold_keyed_terms_eq_filter_sum
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



theorem list_filter_eq_slice_of_partition
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

end ConnesRigidity.AffineSymplecticOrbitCertificate

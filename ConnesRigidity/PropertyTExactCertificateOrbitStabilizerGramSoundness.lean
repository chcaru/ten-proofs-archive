


import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerValidation


namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section


private theorem orbitArray_toList_getD {α : Type} (rows : Array α)
    (index : Nat) (fallback : α) :
    rows.toList.getD index fallback = rows.getD index fallback := by
  simp [List.getD_eq_getElem?_getD,
    Array.getD_eq_getD_getElem?, Array.getElem?_toList]


private theorem orbitFindImageRow_sound
    (target : Nat) (rows : List (Array Int)) (position : Nat)
    (row : Array Int) (remaining : List (Array Int)) (next : Nat)
    (hresult : orbitFindImageRow target rows position =
      some (row, remaining, next)) :
    position ≤ target ∧
      ∃ hindex : target - position < rows.length,
        rows[target - position] = row ∧
          remaining = rows.drop (target - position + 1) ∧
          next = target + 1 := by
  induction rows generalizing position with
  | nil => simp [orbitFindImageRow] at hresult
  | cons head tail ih =>
      simp only [orbitFindImageRow] at hresult
      split at hresult
      next heq =>
        obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hresult
        subst target
        simp
      next hne =>
        obtain ⟨hposition, hlength, hrow, hremaining, hnext⟩ :=
          ih (position + 1) hresult
        have htarget : position < target := by omega
        have hsub : target - position = (target - (position + 1)) + 1 := by
          omega
        refine ⟨by omega, by simpa [hsub] using hlength, ?_, ?_, hnext⟩
        · simpa [hsub] using hrow
        · simpa [hsub] using hremaining


private theorem orbitFindImageRow_drop_sound
    (target position : Nat) (rows : List (Array Int))
    (hposition : position ≤ rows.length)
    (row : Array Int) (remaining : List (Array Int)) (next : Nat)
    (hresult : orbitFindImageRow target (rows.drop position) position =
      some (row, remaining, next)) :
    ∃ htarget : target < rows.length,
      row = rows[target] ∧
        remaining = rows.drop (target + 1) ∧
        next = target + 1 := by
  obtain ⟨hle, hindex, hrow, hremaining, hnext⟩ :=
    orbitFindImageRow_sound target (rows.drop position) position
      row remaining next hresult
  have htarget : target < rows.length := by
    simp only [List.length_drop] at hindex
    omega
  refine ⟨htarget, ?_, ?_, hnext⟩
  · symm
    calc
      rows[target] = (rows.drop position)[target - position] := by
        rw [List.getElem_drop]
        congr 1
        omega
      _ = row := hrow
  · rw [hremaining, List.drop_drop]
    congr 1
    omega




theorem orbitGramTransposeAux_sound
    (rows : List (Array Int)) (previousLeft : Nat)
    (leftImages : Array Int) (cursor : List (Array Int)) (position : Nat)
    (hcursor : cursor = basisPermutationTransposeData.toList.drop position)
    (hleft : leftImages =
      basisPermutationTransposeData.getD previousLeft #[])
    (hcheck : orbitGramTransposeAux basisPermutationTransposeData.toList
      rows previousLeft leftImages cursor position = true) :
    ∀ row ∈ rows,
      orbitGramTransposeRow
        (basisPermutationTransposeData.getD
          (orbitEntry row 0).toNat #[])
        (basisPermutationTransposeData.getD
          (orbitEntry row 1).toNat #[]) row = true := by
  induction rows generalizing previousLeft leftImages cursor position with
  | nil => simp
  | cons row rows ih =>
      simp only [orbitGramTransposeAux] at hcheck
      split at hcheck
      next hsame =>
        split at hcheck
        next => contradiction
        next rightImages remaining next hfind =>
          simp only [Bool.and_eq_true] at hcheck
          obtain ⟨hrightIndex, hrightImages, hremaining, hnext⟩ :=
            orbitFindImageRow_drop_sound (orbitEntry row 1).toNat
              position basisPermutationTransposeData.toList
              (by
                subst cursor
                obtain ⟨hle, hindex, _⟩ := orbitFindImageRow_sound
                  (orbitEntry row 1).toNat
                  (basisPermutationTransposeData.toList.drop position)
                  position rightImages remaining next hfind
                simp only [List.length_drop] at hindex
                omega)
              rightImages remaining next (by simpa [hcursor] using hfind)
          have hright : rightImages =
              basisPermutationTransposeData.getD
                (orbitEntry row 1).toNat #[] := by
            rw [hrightImages]
            symm
            rw [← orbitArray_toList_getD]
            exact List.getD_eq_getElem
              basisPermutationTransposeData.toList #[] hrightIndex
          have hleft' : leftImages =
              basisPermutationTransposeData.getD
                (orbitEntry row 0).toNat #[] := by
            simpa [hsame] using hleft
          have htail := ih (orbitEntry row 0).toNat leftImages
            remaining next (by simpa [hnext] using hremaining)
              hleft' hcheck.2
          intro candidate hcandidate
          simp only [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hcandidate
          · simpa [← hleft', ← hright] using hcheck.1
          · exact htail candidate hcandidate
      next hnew =>
        split at hcheck
        next => contradiction
        next rightImages remaining next hfind =>
          simp only [Bool.and_eq_true] at hcheck
          obtain ⟨hrightIndex, hrightImages, hremaining, hnext⟩ :=
            orbitFindImageRow_drop_sound (orbitEntry row 1).toNat
              0 basisPermutationTransposeData.toList (by omega)
              rightImages remaining next (by simpa using hfind)
          have hright : rightImages =
              basisPermutationTransposeData.getD
                (orbitEntry row 1).toNat #[] := by
            rw [hrightImages]
            symm
            rw [← orbitArray_toList_getD]
            exact List.getD_eq_getElem
              basisPermutationTransposeData.toList #[] hrightIndex
          have htail := ih (orbitEntry row 0).toNat
            (basisPermutationTransposeData.getD
              (orbitEntry row 0).toNat #[])
            remaining next
            (by simpa [hnext] using hremaining)
            rfl hcheck.2
          intro candidate hcandidate
          simp only [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hcandidate
          · simpa [← hright] using hcheck.1
          · exact htail candidate hcandidate



private theorem orbitZip_foldl_eq_range_foldl
    (left right : Array Int) (size : Nat)
    (hleft : left.size = size) (hright : right.size = size)
    (value : Int → Int → Nat) :
    (left.toList.zip right.toList).foldl
        (fun total pair => total + value pair.1 pair.2) 0 =
      (List.range size).foldl
        (fun total index => total +
          value (left.getD index 0) (right.getD index 0)) 0 := by
  have heq : left.toList.zip right.toList =
      (List.range size).map
        (fun index => (left.getD index 0, right.getD index 0)) := by
    apply List.ext_getElem
    · simp [List.length_zip, hleft, hright]
    · intro index hfirst hsecond
      have hleftIndex : index < left.size := by
        simpa [hleft] using hsecond
      have hrightIndex : index < right.size := by
        simpa [hright] using hsecond
      simp only [List.getElem_zip, Array.getElem_toList,
        List.getElem_map, List.getElem_range]
      apply Prod.ext <;> simp [hleftIndex, hrightIndex]
  rw [heq, List.foldl_map]



private theorem orbitList_foldl_congr_mem {α β : Type}
    (rows : List α) (first second : β → α → β)
    (hstep : ∀ total entry, entry ∈ rows →
      first total entry = second total entry)
    (initial : β) :
    rows.foldl first initial = rows.foldl second initial := by
  induction rows generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [hstep initial head (by simp)]
      apply ih
      intro total entry hentry
      exact hstep total entry (by simp [hentry])



theorem orbitGramTransposeFold_eq_stabilizerCount
    (left right : Nat)
    (hleft : left < basisData.size)
    (hright : right < basisData.size) :
    ((basisPermutationTransposeData.getD left #[]).toList.zip
        (basisPermutationTransposeData.getD right #[]).toList).foldl
      (orbitGramTransposeStep left right) 0 =
        orbitGramStabilizerCount left right := by
  obtain ⟨hpermutationSize, htransposeSize, hwidths, hcompatibility⟩ :=
    orbitTransposeCompatibilityCheck_sound
      orbitTransposeCompatibilityCheck_valid
  have hleftTranspose : left < basisPermutationTransposeData.size := by
    simpa [htransposeSize] using hleft
  have hrightTranspose : right < basisPermutationTransposeData.size := by
    simpa [htransposeSize] using hright
  have hleftWidth :
      (basisPermutationTransposeData.getD left #[]).size =
        symmetryData.size := by
    rw [← Array.getElem_eq_getD (fallback := #[]) (h := hleftTranspose)]
    exact hwidths left hleftTranspose
  have hrightWidth :
      (basisPermutationTransposeData.getD right #[]).size =
        symmetryData.size := by
    rw [← Array.getElem_eq_getD (fallback := #[]) (h := hrightTranspose)]
    exact hwidths right hrightTranspose
  let indicator (imageLeft imageRight : Int) : Nat :=
    (if imageLeft.toNat = left ∧ imageRight.toNat = right then 1 else 0) +
      (if imageLeft.toNat = right ∧ imageRight.toNat = left then 1 else 0)
  calc
    _ = ((basisPermutationTransposeData.getD left #[]).toList.zip
        (basisPermutationTransposeData.getD right #[]).toList).foldl
          (fun total images => total + indicator images.1 images.2) 0 := by
            apply congrArg
              (fun step =>
                ((basisPermutationTransposeData.getD left #[]).toList.zip
                  (basisPermutationTransposeData.getD right #[]).toList).foldl
                    step 0)
            funext total images
            simp [orbitGramTransposeStep, indicator, Nat.add_assoc]
    _ = (List.range symmetryData.size).foldl
          (fun total symmetry => total + indicator
            ((basisPermutationTransposeData.getD left #[]).getD symmetry 0)
            ((basisPermutationTransposeData.getD right #[]).getD symmetry 0))
          0 := orbitZip_foldl_eq_range_foldl _ _ _
            hleftWidth hrightWidth indicator
    _ = orbitGramStabilizerCount left right := by
      unfold orbitGramStabilizerCount
      apply orbitList_foldl_congr_mem
      intro total symmetry hsymmetry
      have hsymmetry' : symmetry < basisPermutationData.size := by
        rw [hpermutationSize]
        exact List.mem_range.mp hsymmetry
      rw [hcompatibility symmetry hsymmetry' left hleft,
        hcompatibility symmetry hsymmetry' right hright]
      simp [indicator, symmetryBasisImage, dataEntry, Nat.add_assoc]



theorem orbitGramStabilizerRowCheck_of_transpose
    (index : Nat) (row : Array Int)
    (hrow : gramOrbitData[index]? = some row)
    (hcheck :
      orbitGramTransposeRow
        (basisPermutationTransposeData.getD
          (orbitEntry row 0).toNat #[])
        (basisPermutationTransposeData.getD
          (orbitEntry row 1).toNat #[]) row = true) :
    orbitGramStabilizerRowCheck index = true := by
  simp only [orbitGramTransposeRow, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨hleft, hright⟩, hpositive⟩, hcounter⟩ := hcheck
  have hleft' := orbitIndexCheck_sound (orbitEntry row 0)
    basisData.size hleft
  have hright' := orbitIndexCheck_sound (orbitEntry row 1)
    basisData.size hright
  have hleftBound : (orbitEntry row 0).toNat < basisData.size := by
    exact (Int.toNat_lt hleft'.1).2 hleft'.2
  have hrightBound : (orbitEntry row 1).toNat < basisData.size := by
    exact (Int.toNat_lt hright'.1).2 hright'.2
  simp only [orbitGramStabilizerRowCheck, hrow, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨⟨hleft, hright⟩, hpositive⟩, ?_⟩
  rw [orbitGramTransposeFold_eq_stabilizerCount _ _
    hleftBound hrightBound] at hcounter
  exact hcounter



theorem orbitGramStabilizerCheck_valid :
    orbitGramStabilizerCheck = true := by
  unfold orbitGramStabilizerCheck
  apply List.all_eq_true.mpr
  intro index hindex
  have hindex' : index < gramOrbitData.size :=
    List.mem_range.mp hindex
  have hrow : gramOrbitData[index]? = some gramOrbitData[index] := by
    simp [hindex']
  apply orbitGramStabilizerRowCheck_of_transpose index
    gramOrbitData[index] hrow
  have hstream := orbitGramTransposeAux_sound gramOrbitData.toList 0
    (basisPermutationTransposeData.getD 0 #[])
    basisPermutationTransposeData.toList 0 rfl rfl
    (by simpa [orbitGramTransposeCheck] using
      orbitGramTransposeCheck_valid)
  exact hstream _ (Array.getElem_mem_toList hindex')

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

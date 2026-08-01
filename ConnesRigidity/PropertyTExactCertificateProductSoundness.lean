


import ConnesRigidity.PropertyTExactCertificateProductBase









namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

private theorem array_getD_toArray (xs : List α) (i : ℕ) (d : α) :
    xs.toArray.getD i d = xs.getD i d := by
  rw [Array.getD]
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · rename_i h
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (Nat.le_of_not_gt h)]
    rfl

private theorem arrayRowData_getD
    (data : Array (Array ℤ)) (i : ℕ) :
    (data.toList.map Array.toList).getD i [] =
      (data.getD i #[]).toList := by
  rw [List.getD_map]
  have h :
      data.getD i #[] = data.toList.getD i #[] := by
    simpa only [Array.toArray_toList] using
      (array_getD_toArray data.toList i #[])
  exact congrArg Array.toList h.symm

private theorem rawAffineProductMatchesArray_toList
    {x y z : Array ℤ}
    (h : rawAffineProductMatchesArray x y z = true) :
    rawAffineProductMatches x.toList y.toList z.toList = true := by
  simpa [rawAffineProductMatches] using h

private theorem range_four : List.range 4 = [0, 1, 2, 3] := by
  rfl

theorem rawAffineProductMatches_matrix
    {x y z : List ℤ} (h : rawAffineProductMatches x y z = true)
    (i j : Fin 4) :
    z.getD (4 * i + j) 0 =
      ((List.range 4).map fun k ↦
        x.getD (4 * i + k) 0 * y.getD (4 * k + j) 0).sum := by
  simp only [rawAffineProductMatches] at h
  rw [rawAffineProductMatchesArray_eq_spec] at h
  simp only [rawAffineProductMatchesArraySpec] at h
  have hi := List.all_eq_true.mp h i (List.mem_range.mpr i.isLt)
  simp only [Bool.and_eq_true] at hi
  have hij :=
    List.all_eq_true.mp hi.2 j (List.mem_range.mpr j.isLt)
  simpa only [array_getD_toArray] using (of_decide_eq_true hij)

theorem rawAffineProductMatches_vector
    {x y z : List ℤ} (h : rawAffineProductMatches x y z = true)
    (i : Fin 4) :
    z.getD (16 + i) 0 =
      x.getD (16 + i) 0 +
        ((List.range 4).map fun k ↦
          x.getD (4 * i + k) 0 * y.getD (16 + k) 0).sum := by
  simp only [rawAffineProductMatches] at h
  rw [rawAffineProductMatchesArray_eq_spec] at h
  simp only [rawAffineProductMatchesArraySpec] at h
  have hi := List.all_eq_true.mp h i (List.mem_range.mpr i.isLt)
  simp only [Bool.and_eq_true] at hi
  simpa only [array_getD_toArray] using (of_decide_eq_true hi.1)

private theorem matrixOfData_mul_eq_of_rawAffineProductMatches
    {x y z : List ℤ} (h : rawAffineProductMatches x y z = true) :
    matrixOfData x * matrixOfData y = matrixOfData z := by
  ext i j
  have hij :=
    rawAffineProductMatches_matrix h (certificateIndex i) (certificateIndex j)
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [matrixOfData_apply, Matrix.mul_apply,
      certificateIndex, range_four]
      at hij ⊢ <;>
    simpa only [add_assoc] using hij.symm

theorem isSymplecticData_middle_of_rawAffineProductMatches
    {x y z : List ℤ}
    (hx : isSymplecticData x = true)
    (hz : isSymplecticData z = true)
    (h : rawAffineProductMatches x y z = true) :
    isSymplecticData y = true := by
  let xg : Matrix.symplecticGroup (Fin 2) ℤ :=
    ⟨matrixOfData x, matrixOfData_mem_symplectic hx⟩
  let zg : Matrix.symplecticGroup (Fin 2) ℤ :=
    ⟨matrixOfData z, matrixOfData_mem_symplectic hz⟩
  have hmatrix :=
    matrixOfData_mul_eq_of_rawAffineProductMatches h
  have hy :
      matrixOfData y =
        (↑(xg⁻¹ * zg) : Matrix SymplecticIndex SymplecticIndex ℤ) := by
    calc
      matrixOfData y =
          (1 : Matrix SymplecticIndex SymplecticIndex ℤ) *
            matrixOfData y := by simp
      _ = (↑(xg⁻¹ * xg) :
              Matrix SymplecticIndex SymplecticIndex ℤ) *
            matrixOfData y := by simp
      _ = (↑xg⁻¹ : Matrix SymplecticIndex SymplecticIndex ℤ) *
            (matrixOfData x * matrixOfData y) := by
              change
                ((↑xg⁻¹ : Matrix SymplecticIndex SymplecticIndex ℤ) *
                    matrixOfData x) * matrixOfData y =
                  (↑xg⁻¹ : Matrix SymplecticIndex SymplecticIndex ℤ) *
                    (matrixOfData x * matrixOfData y)
              rw [Matrix.mul_assoc]
      _ = (↑xg⁻¹ : Matrix SymplecticIndex SymplecticIndex ℤ) *
            matrixOfData z := by rw [hmatrix]
      _ = (↑(xg⁻¹ * zg) :
              Matrix SymplecticIndex SymplecticIndex ℤ) := by rfl
  apply decide_eq_true
  rw [hy]
  have hmem := (xg⁻¹ * zg).property
  rw [SymplecticGroup.mem_iff] at hmem
  intro i j
  exact congrFun (congrFun hmem i) j



theorem gammaZeroOfData_mul_eq_of_rawAffineProductMatches
    {x y z : List ℤ}
    (hx : isSymplecticData x = true)
    (hy : isSymplecticData y = true)
    (hz : isSymplecticData z = true)
    (h : rawAffineProductMatches x y z = true) :
    gammaZeroOfData x * gammaZeroOfData y = gammaZeroOfData z := by
  apply CocycleExtension.ext
  · funext i
    simp only [gammaZeroOfData, hx, hy, hz,
      CocycleExtension.mul_fst, NormalizedAddCocycle.zero_apply, add_zero]
    change
      vectorOfData x i + (matrixOfData x).mulVec (vectorOfData y) i =
        vectorOfData z i
    have hi := rawAffineProductMatches_vector h (certificateIndex i)
    rcases i with i | i <;> fin_cases i <;>
      norm_num [matrixOfData_apply, vectorOfData_apply,
        Matrix.mulVec, certificateIndex]
        at hi ⊢ <;>
      exact hi.symm
  · apply Subtype.ext
    ext i j
    simp only [gammaZeroOfData, hx, hy, hz, CocycleExtension.mul_snd]
    change (matrixOfData x * matrixOfData y) i j = matrixOfData z i j
    have hij :=
      rawAffineProductMatches_matrix h (certificateIndex i) (certificateIndex j)
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [matrixOfData_apply, Matrix.mul_apply,
        certificateIndex, range_four]
        at hij ⊢ <;>
      simpa only [add_assoc] using hij.symm

private theorem getD_mem_of_lt {l : List α} {i : ℕ} {d : α}
    (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem ..

private theorem productIndexEntriesAreValid_getD
    {left : Array ℤ} {indices : List ℤ}
    {rights : List (Array ℤ)}
    (h : productIndexEntriesAreValid left indices rights = true)
    (j : ℕ) (hj : j < indices.length) :
    productIndexEntryIsValid left
      (indices.getD j 0) (rights.getD j #[]) = true := by
  induction indices generalizing rights j with
  | nil =>
      simp at hj
  | cons index indices ih =>
      cases rights with
      | nil =>
          simp [productIndexEntriesAreValid] at h
      | cons right rights =>
          simp only [productIndexEntriesAreValid,
            Bool.and_eq_true] at h
          cases j with
          | zero =>
              simpa using h.1
          | succ j =>
              simp only [List.length_cons,
                Nat.succ_lt_succ_iff] at hj
              simpa using ih h.2 j hj



theorem productIndexDataRow_size_of_row_checks
    (productChecks :
      ∀ i : Fin 425, productIndexRowIsValid i = true)
    (i : Fin 425) :
    (productIndexDataRow i).size = 425 := by
  have hi := productChecks i
  simp only [productIndexRowIsValid,
    Bool.and_eq_true] at hi
  exact of_decide_eq_true hi.1

private theorem productIndex_component_of_checks
    (productChecks :
      ∀ i : Fin 425, productIndexRowIsValid i = true)
    (i j : Fin 425) :
    let k : ℕ :=
      (productIndexDataRow i).getD j 0 |>.toNat
    k < 73033 ∧
      rawAffineProductMatchesArray
        (basisDataArray.getD i #[])
        (allElementDataRow k)
        (basisDataArray.getD j #[]) = true := by
  have hi := productChecks i
  simp only [productIndexRowIsValid,
    Bool.and_eq_true] at hi
  have hsize :=
    productIndexDataRow_size_of_row_checks productChecks i
  have hj' :
      j.val < (productIndexDataRow i).toList.length := by
    simp [hsize]
  have hentry :=
    productIndexEntriesAreValid_getD hi.2 j hj'
  have hindex :
      (productIndexDataRow i).toList.getD j 0 =
        (productIndexDataRow i).getD j 0 := by
    simpa only [Array.toArray_toList] using
      (array_getD_toArray
        (productIndexDataRow i).toList j 0).symm
  have hright :
      basisDataArray.toList.getD j #[] =
        basisDataArray.getD j #[] := by
    simpa only [Array.toArray_toList] using
      (array_getD_toArray basisDataArray.toList j #[]).symm
  rw [hindex, hright] at hentry
  simp only [productIndexEntryIsValid,
    Bool.and_eq_true] at hentry
  exact ⟨of_decide_eq_true hentry.1, hentry.2⟩



theorem tableElement_index_product_valid_of_row_checks
    (basisDataLength : basisData.length = 425)
    (basisSymplectic : basisDataIsSymplectic = true)
    (productChecks :
      ∀ i : Fin 425, productIndexRowIsValid i = true)
    (i j : Fin 425) :
    tableElement (tableIndex i j) =
      (certificateBasis i)⁻¹ * certificateBasis j := by
  have hbi :
      isSymplecticData (basisData.getD i []) = true := by
    exact List.all_eq_true.mp basisSymplectic _
      (getD_mem_of_lt (by simp [basisDataLength]))
  have hbj :
      isSymplecticData (basisData.getD j []) = true := by
    exact List.all_eq_true.mp basisSymplectic _
      (getD_mem_of_lt (by simp [basisDataLength]))
  have hcomponent := productIndex_component_of_checks productChecks i j
  have hk :
      productIndex i j < 73033 := by
    simpa only [productIndex] using hcomponent.1
  have hm :
      rawAffineProductMatches
          (basisData.getD i [])
          (allElementDataRow (productIndex i j)).toList
          (basisData.getD j []) = true := by
    rw [basisData, arrayRowData_getD]
    rw [arrayRowData_getD]
    apply rawAffineProductMatchesArray_toList
    simpa only [productIndex] using hcomponent.2
  have hae :
      isSymplecticData
        (allElementDataRow (productIndex i j)).toList = true :=
    isSymplecticData_middle_of_rawAffineProductMatches hbi hbj hm
  rw [tableElement, tableIndex, Fin.val_ofNat, Nat.mod_eq_of_lt hk]
  apply inv_mul_eq_iff_eq_mul.mp
  simp only [certificateBasis]
  simpa [allElement, basisElement] using
    gammaZeroOfData_mul_eq_of_rawAffineProductMatches hbi hae hbj hm

end AffineSymplecticCertificate

end ConnesRigidity

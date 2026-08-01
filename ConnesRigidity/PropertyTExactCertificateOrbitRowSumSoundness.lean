


import ConnesRigidity.PropertyTExactCertificateOrbitCheckerSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidation
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidation
import ConnesRigidity.PropertyTExactCertificateOrbitTransportValidation










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable section



private theorem orbitRowBasisData_size : basisData.size = 425 := by
  decide +kernel



private theorem orbitRowSymmetryData_size : symmetryData.size = 64 := by
  decide +kernel


private theorem orbitRowSymmetryBasisImage_lt
    (symmetry : Fin 64) (index : Fin 425) :
    symmetryBasisImage symmetry.val index.val < 425 := by
  have hpermutation := orbitBasisPermutationCheck_sound
    orbitBasisPermutationCheck_valid
  have hsymmetry : symmetry.val < basisPermutationData.size := by
    rw [hpermutation.1, orbitRowSymmetryData_size]
    exact symmetry.isLt
  cases hrow : basisPermutationData[symmetry.val]? with
  | none => simp [hsymmetry] at hrow
  | some entries =>
      have hcheck := hpermutation.2 symmetry.val hsymmetry
      simp only [orbitBasisPermutationRowCheck, hrow, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      have hindex : index.val < entries.size := by
        rw [hcheck.1, orbitRowBasisData_size]
        exact index.isLt
      have hentry := List.all_eq_true.mp hcheck.2 entries[index.val]
        (Array.getElem_mem_toList hindex)
      have hbound := orbitIndexCheck_sound entries[index.val]
        basisData.size hentry
      change (dataEntry basisPermutationData symmetry.val index.val).toNat < 425
      have hfield : dataEntry basisPermutationData symmetry.val index.val =
          entries[index.val] := by
        simp [dataEntry, Array.getD_eq_getD_getElem?, hrow, hindex]
      rw [hfield]
      have hbound' := (Int.toNat_lt hbound.1).2 hbound.2
      simpa only [orbitRowBasisData_size] using hbound'



private theorem orbitRowSymmetryInverse_properties
    (symmetry : Fin 64) (index : Fin 425) :
    inverseSymmetry symmetry.val < 64 ∧
      symmetryBasisImage (inverseSymmetry symmetry.val)
        (symmetryBasisImage symmetry.val index.val) = index.val ∧
      symmetryBasisImage symmetry.val
        (symmetryBasisImage (inverseSymmetry symmetry.val) index.val) =
        index.val := by
  have hinverse := orbitSymmetryInverseCheck_sound
    orbitSymmetryInverseCheck_valid
  have hsymmetry : symmetry.val < symmetryInverseData.size := by
    rw [hinverse.1, orbitRowSymmetryData_size]
    exact symmetry.isLt
  cases hrow : symmetryInverseData[symmetry.val]? with
  | none => simp [hsymmetry] at hrow
  | some entries =>
      have hcheck := hinverse.2 symmetry.val hsymmetry
      simp only [orbitSymmetryInverseRowCheck, hrow,
        Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range, and_assoc] at hcheck
      have hindex : index.val < basisData.size := by
        rw [orbitRowBasisData_size]
        exact index.isLt
      have hentry := hcheck.2.2 index.val hindex
      have hentry' :
          symmetry.val < symmetryData.size ∧
            inverseSymmetry symmetry.val < symmetryData.size ∧
            index.val < basisData.size ∧
            symmetryBasisImage (inverseSymmetry symmetry.val)
              (symmetryBasisImage symmetry.val index.val) = index.val ∧
            symmetryBasisImage symmetry.val
              (symmetryBasisImage (inverseSymmetry symmetry.val) index.val) =
              index.val := by
        simpa only [orbitSymmetryInverseEntryCheck, Bool.and_eq_true,
          decide_eq_true_eq, and_assoc] using hentry
      exact ⟨by simpa [orbitRowSymmetryData_size] using hentry'.2.1,
        hentry'.2.2.2⟩




private noncomputable def orbitRowBasisPermutation
    (symmetry : Fin 64) : Equiv.Perm (Fin 425) where
  toFun index :=
    ⟨symmetryBasisImage symmetry.val index.val,
      orbitRowSymmetryBasisImage_lt symmetry index⟩
  invFun index :=
    ⟨symmetryBasisImage (inverseSymmetry symmetry.val) index.val,
      orbitRowSymmetryBasisImage_lt
        ⟨inverseSymmetry symmetry.val,
          (orbitRowSymmetryInverse_properties symmetry index).1⟩ index⟩
  left_inv index := Fin.ext
    (orbitRowSymmetryInverse_properties symmetry index).2.1
  right_inv index := Fin.ext
    (orbitRowSymmetryInverse_properties symmetry index).2.2


theorem orbitArrayListFoldl_eq_fin_sum (rows : Array Int) (value : Int → Int) :
    rows.toList.foldl (fun total entry => total + value entry) 0 =
      ∑ index : Fin rows.size, value rows[index.val] := by
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  have hlist : rows.toList.map value =
      List.ofFn (fun index : Fin rows.size => value rows[index.val]) := by
    apply List.ext_getElem
    · simp
    · intro index hleft hright
      simp
  rw [hlist, List.sum_ofFn]



theorem orbitNormalizedRowGramSum_eq_fin_sum (row : Fin 26) :
    orbitNormalizedRowGramSum row.val =
      ∑ index : Fin 425,
        gramOrbitCoefficient
          (dataEntry pairOrbitIndexData row.val index.val).toNat := by
  have hcoverage := orbitPairCoverageCheck_sound orbitPairCoverageCheck_valid
  have hrowbound : row.val < pairOrbitIndexData.size := by
    rw [hcoverage.1, basisOrbitRepresentativeData_size]
    exact row.isLt
  cases hrow : pairOrbitIndexData[row.val]? with
  | none => simp [hrowbound] at hrow
  | some entries =>
      have hentrysize :=
        (orbitPairCoverageRowCheck_sound row.val entries hrow
          (hcoverage.2 row.val hrowbound)).1
      rw [orbitRowBasisData_size] at hentrysize
      have hget : pairOrbitIndexData.getD row.val #[] = entries := by
        simp [Array.getD_eq_getD_getElem?, hrow]
      unfold orbitNormalizedRowGramSum
      rw [hget, orbitArrayListFoldl_eq_fin_sum]
      refine Fintype.sum_equiv (finCongr hentrysize)
        (fun index : Fin entries.size =>
          gramOrbitCoefficient (entries[index.val]).toNat)
        (fun index : Fin 425 =>
          gramOrbitCoefficient
            (dataEntry pairOrbitIndexData row.val index.val).toNat)
        ?_
      intro index
      simp [dataEntry, Array.getD_eq_getD_getElem?, hrow, index.isLt]




theorem orbitNormalizedGramRow_sum_zero (row : Fin 26) :
    (∑ index : Fin 425,
      gramOrbitCoefficient
        (dataEntry pairOrbitIndexData row.val index.val).toNat) = 0 := by
  rw [← orbitNormalizedRowGramSum_eq_fin_sum]
  exact orbitNormalizedRowGramSum_zero row





theorem orbitBasisTransport_indices_lt (index : Fin 425) :
    basisOrbit index.val < 26 ∧ basisTransportSymmetry index.val < 64 := by
  have htransport := orbitBasisTransportCheck_sound
    orbitBasisTransportCheck_valid
  have hindex : index.val < basisTransporterData.size := by
    rw [htransport.1, orbitRowBasisData_size]
    exact index.isLt
  let row := basisTransporterData[index.val]
  have hrow : basisTransporterData[index.val]? = some row := by
    simp [row, hindex]
  obtain ⟨_hwidth, horbit, hsymmetry, _himage⟩ :=
    orbitBasisTransportRowCheck_sound index.val row hrow
      (htransport.2 index.val hindex)
  constructor
  · change (dataEntry basisTransporterData index.val 0).toNat < 26
    have hfield :
        dataEntry basisTransporterData index.val 0 = orbitEntry row 0 := by
      simp [dataEntry, Array.getD_eq_getD_getElem?, hrow, orbitEntry]
    rw [hfield]
    have hsize : basisOrbitRepresentativeData.size = 26 :=
      basisOrbitRepresentativeData_size
    apply (Int.toNat_lt horbit.1).2
    simpa [hsize] using horbit.2
  · change (dataEntry basisTransporterData index.val 1).toNat < 64
    have hfield :
        dataEntry basisTransporterData index.val 1 = orbitEntry row 1 := by
      simp [dataEntry, Array.getD_eq_getD_getElem?, hrow, orbitEntry]
    rw [hfield]
    apply (Int.toNat_lt hsymmetry.1).2
    simpa [orbitRowSymmetryData_size] using hsymmetry.2





theorem orbitGram_integer_rowSum (row : Fin 425) :
    (∑ column : Fin 425, gramEntry row.val column.val) = 0 := by
  obtain ⟨horbit, hsymmetry⟩ := orbitBasisTransport_indices_lt row
  let symmetry : Fin 64 :=
    ⟨basisTransportSymmetry row.val, hsymmetry⟩
  let permutation := (orbitRowBasisPermutation symmetry).symm
  calc
    (∑ column : Fin 425, gramEntry row.val column.val) =
        ∑ column : Fin 425,
          gramOrbitCoefficient
            (dataEntry pairOrbitIndexData (basisOrbit row.val)
              (permutation column).val).toNat := by
      apply Finset.sum_congr rfl
      intro column _
      change
        gramOrbitCoefficient
            (dataEntry pairOrbitIndexData (basisOrbit row.val)
              (symmetryBasisImage
                (inverseSymmetry (basisTransportSymmetry row.val))
                column.val)).toNat =
          gramOrbitCoefficient
            (dataEntry pairOrbitIndexData (basisOrbit row.val)
              (permutation column).val).toNat
      rfl
    _ = ∑ column : Fin 425,
          gramOrbitCoefficient
            (dataEntry pairOrbitIndexData (basisOrbit row.val)
              column.val).toNat :=
      Equiv.sum_comp permutation
        (fun column : Fin 425 =>
          gramOrbitCoefficient
            (dataEntry pairOrbitIndexData (basisOrbit row.val)
              column.val).toNat)
    _ = 0 := orbitNormalizedGramRow_sum_zero
      ⟨basisOrbit row.val, horbit⟩



theorem orbitGram_rowSum (row : Fin 425) :
    (∑ column : Fin 425, (gramEntry row.val column.val : ℚ)) = 0 := by
  exact_mod_cast orbitGram_integer_rowSum row

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

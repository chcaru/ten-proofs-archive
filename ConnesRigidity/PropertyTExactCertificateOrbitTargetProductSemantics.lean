


import ConnesRigidity.PropertyTExactCertificateOrbitTargetCoefficients
import ConnesRigidity.PropertyTExactCertificateOrbitTargetWitness
import Mathlib.Data.List.GetD












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

local instance : DecidableEq constructedGammaZeroGroup :=
  generatorEnumerationDecidableEq


theorem target_countP_eq_fin_sum {α : Type*}
    (rows : List α) (predicate : α → Bool) :
    (rows.countP predicate : Int) =
      ∑ index : Fin rows.length,
        if predicate rows[index.val] then (1 : Int) else 0 := by
  rw [Fin.sum_univ_fun_getElem rows
    (fun row => if predicate row then (1 : Int) else 0)]
  induction rows with
  | nil => simp
  | cons row rows inductionHypothesis =>
      simp only [List.countP_cons, List.map_cons, List.sum_cons]
      cases predicate row <;>
        simp [inductionHypothesis, add_comm]



theorem target_generatorFinset_sum_eq_fin
    (value : constructedGammaZeroGroup → Int) :
    (∑ generator ∈ gammaZeroElementaryGenerators, value generator) =
      ∑ index : Fin 24, value (generatorElement index.val) := by
  rw [← generatorElements_toFinset_eq,
    List.sum_toFinset value generatorElements_nodup,
    ← Fin.sum_univ_fun_getElem generatorElements value]
  have hlength : generatorElements.length = 24 := by
    simp [generatorElements, generatorData_size]
  apply Fintype.sum_equiv (finCongr hlength)
  intro index
  congr 1
  have hindex : (finCongr hlength index).val < generatorData.size := by
    rw [generatorData_size]
    exact (finCongr hlength index).isLt
  simp only [generatorElements, List.getElem_map, Array.getElem_toList,
    generatorElement]
  simp only [Array.getD]
  split
  next => rfl
  next h => exact (h hindex).elim



theorem targetGeneratorRow_getD_mem (index : Nat) (hindex : index < 24) :
    generatorData.getD index #[] ∈ generatorData.toList := by
  have hsize : index < generatorData.size := by
    rw [generatorData_size]
    exact hindex
  have hmem := Array.mem_toList_iff.mpr (Array.getElem_mem hsize)
  simp [Array.getD, hsize]



theorem targetProductRecord_code_iff_group_product
    (representative : Array Int)
    (hsize : representative.size = 20)
    (hvalid : isSymplecticRow representative = true)
    (hbounded : targetCoordinateBounds representative.toList = true)
    (position : Nat) (record : List Int)
    (hrecord : orbitTargetProductRecordCheck position record = true) :
    record.getD 22 0 = targetCoordinateCode representative.toList ↔
      gammaZeroOfRow (generatorData.getD (record.getD 0 0).toNat #[]) *
        gammaZeroOfRow (generatorData.getD (record.getD 1 0).toNat #[]) =
          gammaZeroOfRow representative := by
  obtain ⟨hlength, hleft, hright, hcoordinatesBounded,
    hcoordinatesValid, hproduct, hcode, _⟩ :=
      orbitTargetProductRecordCheck_sound position record hrecord
  let coordinates := orbitTargetProductRecordCoordinates record
  have hcoordinatesLength : coordinates.length = 20 := by
    simp [coordinates, orbitTargetProductRecordCoordinates, hlength]
  have hleftIndex : (record.getD 0 0).toNat < 24 := by
    exact (Int.toNat_lt hleft.1).mpr hleft.2
  have hrightIndex : (record.getD 1 0).toNat < 24 := by
    exact (Int.toNat_lt hright.1).mpr hright.2
  have hleftValid := targetGeneratorRows_symplectic
    (targetGeneratorRow_getD_mem _ hleftIndex)
  have hrightValid := targetGeneratorRows_symplectic
    (targetGeneratorRow_getD_mem _ hrightIndex)
  have hgroupProduct := rawProductCheck_sound hleftValid hrightValid
    hcoordinatesValid hproduct
  constructor
  · intro hequal
    have hcoordinatesCode :
        targetCoordinateCode coordinates =
          targetCoordinateCode representative.toList := by
      exact hcode.symm.trans hequal
    have hcoordinatesEqual : coordinates = representative.toList :=
      targetCoordinateCode_injective
        (by simpa [hsize] using hcoordinatesLength)
        hcoordinatesBounded hbounded hcoordinatesCode
    simpa [coordinates, hcoordinatesEqual] using hgroupProduct
  · intro hequal
    have hgroupEqual : gammaZeroOfRow coordinates.toArray =
        gammaZeroOfRow representative := hgroupProduct.symm.trans hequal
    have hcoordinatesSize : coordinates.toArray.size = 20 := by
      simpa using hcoordinatesLength
    have harrayEqual : coordinates.toArray = representative :=
      beq_iff_eq.mp
        ((targetRawArray_beq_iff hcoordinatesSize hsize
          hcoordinatesValid hvalid).mpr hgroupEqual)
    have hcoordinatesEqual : coordinates = representative.toList := by
      simpa using congrArg Array.toList harrayEqual
    exact hcode.trans (congrArg targetCoordinateCode hcoordinatesEqual)



noncomputable def targetProductRecordPairCode
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (position : Fin 576) : Fin 576 := by
  have hposition : position.val < targetGeneratorProductRowData.length := by
    omega
  have hrecord := orbitTargetProductRecordsCheck_get
    targetGeneratorProductRowData 0 position.val hposition hrecords
  have hsound :=
    orbitTargetProductRecordCheck_sound position.val
      (targetGeneratorProductRowData.getD position.val [])
      (by simpa using hrecord)
  have hleft := hsound.2.1
  have hright := hsound.2.2.1
  have hleftIndex :
      ((targetGeneratorProductRowData.getD position.val []).getD 0 0).toNat <
        24 := (Int.toNat_lt hleft.1).mpr hleft.2
  have hrightIndex :
      ((targetGeneratorProductRowData.getD position.val []).getD 1 0).toNat <
        24 := (Int.toNat_lt hright.1).mpr hright.2
  exact ⟨24 *
    ((targetGeneratorProductRowData.getD position.val []).getD 0 0).toNat +
      ((targetGeneratorProductRowData.getD position.val []).getD 1 0).toNat,
    by omega⟩


noncomputable def targetProductRecordInversePosition
    (hinversesLength : targetGeneratorProductRowIndexData.length = 576)
    (hinverses : orbitTargetProductInverseCheck 0
      targetGeneratorProductRowIndexData = true)
    (pair : Fin 576) : Fin 576 := by
  have hpair : pair.val < targetGeneratorProductRowIndexData.length := by
    omega
  have hinverse := orbitTargetProductInverseCheck_get
    targetGeneratorProductRowIndexData 0 pair.val hpair hinverses
  dsimp at hinverse
  exact ⟨((targetGeneratorProductRowIndexData.getD pair.val []).getD
    0 (-1)).toNat, (Int.toNat_lt hinverse.1).mpr hinverse.2.1⟩

@[simp] theorem targetProductRecordPairCode_val
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (position : Fin 576) :
    (targetProductRecordPairCode hrecordsLength hrecords position).val =
      24 * ((targetGeneratorProductRowData.getD position.val []).getD
        0 0).toNat +
        ((targetGeneratorProductRowData.getD position.val []).getD
          1 0).toNat := by
  unfold targetProductRecordPairCode
  rfl

@[simp] theorem targetProductRecordInversePosition_val
    (hinversesLength : targetGeneratorProductRowIndexData.length = 576)
    (hinverses : orbitTargetProductInverseCheck 0
      targetGeneratorProductRowIndexData = true)
    (pair : Fin 576) :
    (targetProductRecordInversePosition hinversesLength hinverses pair).val =
      ((targetGeneratorProductRowIndexData.getD pair.val []).getD
        0 (-1)).toNat := by
  unfold targetProductRecordInversePosition
  rfl



noncomputable def targetProductRecordPermutation
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hinversesLength : targetGeneratorProductRowIndexData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (hinverses : orbitTargetProductInverseCheck 0
      targetGeneratorProductRowIndexData = true) : Fin 576 ≃ Fin 576 where
  toFun := targetProductRecordPairCode hrecordsLength hrecords
  invFun := targetProductRecordInversePosition hinversesLength hinverses
  left_inv := by
    intro position
    apply Fin.ext
    have hposition : position.val < targetGeneratorProductRowData.length := by
      omega
    have hrecord := orbitTargetProductRecordsCheck_get
      targetGeneratorProductRowData 0 position.val hposition hrecords
    have hforward :=
      (orbitTargetProductRecordCheck_sound position.val
        (targetGeneratorProductRowData.getD position.val [])
        (by simpa using hrecord)).2.2.2.2.2.2.2
    rw [targetProductRecordInversePosition_val,
      targetProductRecordPairCode_val]
    rw [hforward]
    simp
  right_inv := by
    intro pair
    apply Fin.ext
    have hpair : pair.val < targetGeneratorProductRowIndexData.length := by
      omega
    have hinverse := orbitTargetProductInverseCheck_get
      targetGeneratorProductRowIndexData 0 pair.val hpair hinverses
    dsimp at hinverse
    rw [targetProductRecordPairCode_val,
      targetProductRecordInversePosition_val]
    simpa using hinverse.2.2



theorem targetProductMultiplicity_eq_fin_sum
    (element : constructedGammaZeroGroup) :
    targetProductMultiplicity gammaZeroElementaryGenerators element =
      ∑ left : Fin 24, ∑ right : Fin 24,
        if generatorElement right.val * generatorElement left.val = element
          then (1 : Int) else 0 := by
  unfold targetProductMultiplicity targetGroupIndicator
  rw [target_generatorFinset_sum_eq_fin]
  apply Finset.sum_congr rfl
  intro left _
  rw [← target_generatorFinset_sum_eq_fin
    (fun right =>
      if right * generatorElement left.val = element then (1 : Int) else 0)]
  apply Finset.sum_congr rfl
  intro right _
  split_ifs <;> rfl


noncomputable def targetProductRecordLeft
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (position : Fin 576) : Fin 24 := by
  have hposition : position.val < targetGeneratorProductRowData.length := by
    omega
  have hrecord := orbitTargetProductRecordsCheck_get
    targetGeneratorProductRowData 0 position.val hposition hrecords
  have hleft := (orbitTargetProductRecordCheck_sound position.val
    (targetGeneratorProductRowData.getD position.val [])
      (by simpa using hrecord)).2.1
  exact ⟨((targetGeneratorProductRowData.getD position.val []).getD
    0 0).toNat, (Int.toNat_lt hleft.1).mpr hleft.2⟩


noncomputable def targetProductRecordRight
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (position : Fin 576) : Fin 24 := by
  have hposition : position.val < targetGeneratorProductRowData.length := by
    omega
  have hrecord := orbitTargetProductRecordsCheck_get
    targetGeneratorProductRowData 0 position.val hposition hrecords
  have hright := (orbitTargetProductRecordCheck_sound position.val
    (targetGeneratorProductRowData.getD position.val [])
      (by simpa using hrecord)).2.2.1
  exact ⟨((targetGeneratorProductRowData.getD position.val []).getD
    1 0).toNat, (Int.toNat_lt hright.1).mpr hright.2⟩

@[simp] theorem targetProductRecordLeft_val
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (position : Fin 576) :
    (targetProductRecordLeft hrecordsLength hrecords position).val =
      ((targetGeneratorProductRowData.getD position.val []).getD 0 0).toNat :=
  rfl

@[simp] theorem targetProductRecordRight_val
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (position : Fin 576) :
    (targetProductRecordRight hrecordsLength hrecords position).val =
      ((targetGeneratorProductRowData.getD position.val []).getD 1 0).toNat :=
  rfl



theorem targetProductRecordPermutation_pair
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hinversesLength : targetGeneratorProductRowIndexData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (hinverses : orbitTargetProductInverseCheck 0
      targetGeneratorProductRowIndexData = true)
    (position : Fin 576) :
    (finProdFinEquiv : Fin 24 × Fin 24 ≃ Fin (24 * 24)).symm
        (targetProductRecordPermutation hrecordsLength hinversesLength
          hrecords hinverses position) =
      (targetProductRecordLeft hrecordsLength hrecords position,
        targetProductRecordRight hrecordsLength hrecords position) := by
  apply (finProdFinEquiv : Fin 24 × Fin 24 ≃ Fin (24 * 24)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change
    (targetProductRecordPairCode hrecordsLength hrecords position).val =
      (finProdFinEquiv
        (targetProductRecordLeft hrecordsLength hrecords position,
          targetProductRecordRight hrecordsLength hrecords position)).val
  simp [targetProductRecordPairCode_val, finProdFinEquiv, Nat.add_comm]







theorem orbitTargetProductRecords_countP_eq_targetProductMultiplicity
    (representative : Array Int)
    (hsize : representative.size = 20)
    (hvalid : isSymplecticRow representative = true)
    (hbounded : targetCoordinateBounds representative.toList = true)
    (hrecordsLength : targetGeneratorProductRowData.length = 576)
    (hinversesLength : targetGeneratorProductRowIndexData.length = 576)
    (hrecords : orbitTargetProductRecordsCheck 0
      targetGeneratorProductRowData = true)
    (hinverses : orbitTargetProductInverseCheck 0
      targetGeneratorProductRowIndexData = true) :
    (targetGeneratorProductRowData.countP
      (fun record =>
        decide
          (record.getD 22 0 = targetCoordinateCode representative.toList)) :
      Int) =
        targetProductMultiplicity gammaZeroElementaryGenerators
          (gammaZeroOfRow representative) := by
  rw [target_countP_eq_fin_sum,
    targetProductMultiplicity_eq_fin_sum, Finset.sum_comm,
    ← Fintype.sum_prod_type']
  let recordEquivalence :
      Fin targetGeneratorProductRowData.length ≃ Fin 24 × Fin 24 :=
    (finCongr hrecordsLength).trans
      ((targetProductRecordPermutation hrecordsLength hinversesLength
        hrecords hinverses).trans
          (finProdFinEquiv : Fin 24 × Fin 24 ≃ Fin (24 * 24)).symm)
  apply Fintype.sum_equiv recordEquivalence
  intro index
  let position : Fin 576 := finCongr hrecordsLength index
  let record := targetGeneratorProductRowData.getD position.val []
  have hrecord : orbitTargetProductRecordCheck position.val record = true := by
    have hposition : position.val < targetGeneratorProductRowData.length := by
      omega
    simpa [record] using orbitTargetProductRecordsCheck_get
      targetGeneratorProductRowData 0 position.val hposition hrecords
  have hpair : recordEquivalence index =
      (targetProductRecordLeft hrecordsLength hrecords position,
        targetProductRecordRight hrecordsLength hrecords position) := by
    exact targetProductRecordPermutation_pair hrecordsLength hinversesLength
      hrecords hinverses position
  have hget : record = targetGeneratorProductRowData[index.val] := by
    exact List.getD_eq_getElem targetGeneratorProductRowData [] index.isLt
  rw [← hget, hpair]
  simp only [targetProductRecordLeft_val, targetProductRecordRight_val,
    generatorElement]
  have hiff := targetProductRecord_code_iff_group_product representative
    hsize hvalid hbounded position.val record hrecord
  change
    (if decide
        (record.getD 22 0 = targetCoordinateCode representative.toList)
      then (1 : Int) else 0) =
      if gammaZeroOfRow
            (generatorData.getD (record.getD 0 0).toNat #[]) *
          gammaZeroOfRow
            (generatorData.getD (record.getD 1 0).toNat #[]) =
          gammaZeroOfRow representative then (1 : Int) else 0
  simp only [decide_eq_true_eq, hiff]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

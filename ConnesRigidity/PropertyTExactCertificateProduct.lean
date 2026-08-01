


import ConnesRigidity.PropertyTExactCertificateProductChecks
import ConnesRigidity.PropertyTExactCertificateProductSoundness









namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

local instance gammaZeroDecidableEqProduct :
    DecidableEq IntegralSymplecticCocycleInput.GammaZero :=
  fun x y =>
    decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd)
      ⟨fun h ↦ by cases x; cases y; simp_all,
       fun h ↦ ⟨congrArg CocycleExtension.fst h,
         congrArg CocycleExtension.snd h⟩⟩

set_option maxHeartbeats 0 in

private theorem basisDataArray_size : basisDataArray.size = 425 := by
  unfold basisDataArray
  decide +kernel

theorem basisData_length : basisData.length = 425 := by
  rw [basisData]
  simpa using basisDataArray_size

set_option maxHeartbeats 0 in

theorem basisData_isSymplectic : basisDataIsSymplectic = true := by
  unfold basisDataIsSymplectic basisData basisDataArray
  decide +kernel

set_option maxHeartbeats 0 in

theorem basisElement_zero_check : basisElement 0 = 1 := by
  unfold basisElement basisData basisDataArray
  decide +kernel

set_option maxHeartbeats 0 in

private theorem basisData_generatorList_raw :
    (basisData.drop 1).take 24 = generatorData := by
  unfold basisData basisDataArray generatorData
  decide +kernel

private theorem basisData_generatorPrefix :
    (List.range 24).map (fun i ↦ basisData.getD (i + 1) []) =
      (basisData.drop 1).take 24 := by
  apply List.ext_getElem
  · simp [basisData_length]
  · intro i hi _
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by
      rw [basisData_length]
      omega)]
    simp

theorem basisElement_generatorList_check :
    (List.range 24).map (fun i ↦ basisElement (i + 1)) =
      generatorData.map gammaZeroOfData := by
  have hprefix := congrArg (List.map gammaZeroOfData)
    basisData_generatorPrefix
  have hraw := congrArg (List.map gammaZeroOfData)
    basisData_generatorList_raw
  simpa only [basisElement, List.map_map, Function.comp_def] using
    hprefix.trans hraw



theorem productIndexDataRow_size (i : Fin 425) :
    (productIndexDataRow i).size = 425 :=
  productIndexDataRow_size_of_row_checks
    allProductIndexRowChecks i


theorem tableElement_index_product_valid
    (i j : Fin 425) :
    tableElement (tableIndex i j) =
      (certificateBasis i)⁻¹ * certificateBasis j :=
  tableElement_index_product_valid_of_row_checks
    basisData_length basisData_isSymplectic allProductIndexRowChecks i j

end AffineSymplecticCertificate

end ConnesRigidity

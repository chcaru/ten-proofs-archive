


import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitGeneratorEnumeration










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

local instance : DecidableEq constructedGammaZeroGroup :=
  generatorEnumerationDecidableEq



theorem targetRawArray_beq_iff
    {left right : Array Int}
    (hleftSize : left.size = 20)
    (hrightSize : right.size = 20)
    (hleftValid : isSymplecticRow left = true)
    (hrightValid : isSymplecticRow right = true) :
    (left == right) = true ↔ gammaZeroOfRow left = gammaZeroOfRow right := by
  constructor
  · intro hequal
    exact congrArg gammaZeroOfRow (beq_iff_eq.mp hequal)
  · intro hequal
    apply beq_iff_eq.mpr
    have hraw :=
      (rawRowEq_iff_gammaZeroOfRow hleftValid hrightValid).mpr hequal
    apply Array.ext (hleftSize.trans hrightSize.symm)
    intro index hleftIndex hrightIndex
    have hindex : index < 20 := by omega
    have hcoordinate := rawRowEq_getD hraw hindex
    simpa [Array.getD, hleftIndex, hrightIndex] using hcoordinate


theorem targetIdentityRow_size :
    (basisData.getD 0 #[]).size = 20 := by
  unfold basisData
  decide +kernel


theorem targetIdentityRow_symplectic :
    isSymplecticRow (basisData.getD 0 #[]) = true := by
  unfold basisData
  decide +kernel


theorem targetIdentityRow_gammaZeroOfRow :
    gammaZeroOfRow (basisData.getD 0 #[]) =
      (1 : constructedGammaZeroGroup) := by
  simpa [orbitBasis, basisElement] using orbitBasis_zero



theorem targetIdentityRawRow_beq_iff
    {representative : Array Int}
    (hsize : representative.size = 20)
    (hvalid : isSymplecticRow representative = true) :
    ((basisData.getD 0 #[]) == representative) = true ↔
      (1 : constructedGammaZeroGroup) = gammaZeroOfRow representative := by
  rw [targetRawArray_beq_iff targetIdentityRow_size hsize
    targetIdentityRow_symplectic hvalid, targetIdentityRow_gammaZeroOfRow]



theorem targetGeneratorRows_size
    {row : Array Int} (hrow : row ∈ generatorData.toList) :
    row.size = 20 := by
  have hwidth :
      generatorData.toList.all
        (fun candidate => decide (candidate.size = 20)) = true := by
    unfold generatorData
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hwidth row hrow)


theorem targetGeneratorRows_symplectic
    {row : Array Int} (hrow : row ∈ generatorData.toList) :
    isSymplecticRow row = true := by
  have hvalid : generatorData.toList.all isSymplecticRow = true := by
    unfold generatorData
    decide +kernel
  exact List.all_eq_true.mp hvalid row hrow



theorem target_foldl_count_eq_sum
    {α : Type*} (rows : List α) (predicate : α → Bool) :
    rows.foldl
        (fun count row => if predicate row then count + 1 else count)
        (0 : Int) =
      (rows.map fun row => if predicate row then (1 : Int) else 0).sum := by
  have haux (initial : Int) :
      rows.foldl
          (fun count row => if predicate row then count + 1 else count)
          initial =
        initial +
          (rows.map fun row => if predicate row then (1 : Int) else 0).sum := by
    induction rows generalizing initial with
    | nil => simp
    | cons row rows inductionHypothesis =>
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [inductionHypothesis]
        split <;> omega
  simpa using haux 0



theorem targetGeneratorRawFold_eq_finset_sum
    (representative : Array Int)
    (hsize : representative.size = 20)
    (hvalid : isSymplecticRow representative = true) :
    generatorData.toList.foldl
        (fun count row =>
          if row == representative then count + 1 else count)
        (0 : Int) =
      ∑ generator ∈ gammaZeroElementaryGenerators,
        if generator = gammaZeroOfRow representative then
          (1 : Int)
        else
          0 := by
  rw [← generatorElements_toFinset_eq]
  change
    generatorData.toList.foldl
        (fun count row =>
          if row == representative then count + 1 else count)
        (0 : Int) =
      generatorElements.toFinset.sum fun generator =>
        if generator = gammaZeroOfRow representative then
          (1 : Int)
        else
          0
  rw [List.sum_toFinset _ generatorElements_nodup]
  rw [target_foldl_count_eq_sum]
  unfold generatorElements
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro row hrow
  have hiff := targetRawArray_beq_iff
    (targetGeneratorRows_size hrow) hsize
      (targetGeneratorRows_symplectic hrow) hvalid
  by_cases hequal : gammaZeroOfRow row = gammaZeroOfRow representative
  · have hboolean : (row == representative) = true := hiff.mpr hequal
    simp [hboolean, hequal]
  · have hboolean : (row == representative) = false := by
      cases h : (row == representative) with
      | false => rfl
      | true => exact (hequal (hiff.mp h)).elim
    simp [hboolean, hequal]

end ConnesRigidity.AffineSymplecticOrbitCertificate

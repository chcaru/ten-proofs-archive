


import ConnesRigidity.PropertyTExactCertificateOrbitInvariantWitness
import ConnesRigidity.PropertyTExactCertificateOrbitPairOrbitMembership











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000


theorem orbitGramRowSize_nonneg
    (row : Array Int) (hrow : row ∈ gramOrbitData.toList) :
    0 ≤ orbitEntry row 7 := by
  obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hrow
  have hindex' : index < gramOrbitData.size := by
    simpa using hindex
  have hrow' : gramOrbitData[index]? = some gramOrbitData[index] := by
    simp [hindex']
  have hcheck := List.all_eq_true.mp orbitGramStabilizerCheck_valid
    index (List.mem_range.mpr hindex')
  have hpositive := (orbitGramStabilizerRowCheck_sound
    index gramOrbitData[index] hrow' hcheck).2.2.1
  have hrowValue : row = gramOrbitData[index] := by
    simpa using hvalue.symm
  simpa [hrowValue] using hpositive.le



theorem orbitGramRepresentative_orbit_card_sum :
    (∑ orbit : Fin 2256,
      Fintype.card (MulAction.orbit OrbitSignedSymmetry
        (orbitGramRepresentative orbit))) =
      Fintype.card (Fin 425 × Fin 425) := by
  have hfold := orbitGramOrbitSizeTotalCheck_sound
    orbitGramOrbitSizeTotalCheck_valid
  have hsum := orbitNat_sum_eq_of_int_fold
    gramOrbitData.toList (fun row => orbitEntry row 7)
    orbitGramRowSize_nonneg (425 * 425)
    (by simpa [orbitBasisData_size] using hfold)
  have hlength : gramOrbitData.toList.length = 2256 := by
    simpa only [Array.length_toList] using gramOrbitData_size
  let indexEquivalence : Fin 2256 ≃ Fin gramOrbitData.toList.length :=
    (finCongr hlength).symm
  simp only [Fintype.card_prod, Fintype.card_fin]
  simp_rw [orbitGramRepresentative_orbit_card]
  calc
    (∑ orbit : Fin 2256, (gramOrbitSize orbit.val).toNat) =
        ∑ index : Fin gramOrbitData.toList.length,
          (orbitEntry gramOrbitData.toList[index.val] 7).toNat := by
      apply Fintype.sum_equiv indexEquivalence
      intro orbit
      have hindex : orbit.val < gramOrbitData.size := by
        rw [gramOrbitData_size]
        exact orbit.isLt
      have hequiv : (indexEquivalence orbit).val = orbit.val := by
        rfl
      have hrow : gramOrbitData.toList[(indexEquivalence orbit).val] =
          gramOrbitData[orbit.val] := by
        simpa only [hequiv] using Array.getElem_toList hindex
      change
        (dataEntry gramOrbitData orbit.val 7).toNat =
          (orbitEntry gramOrbitData.toList[
            (indexEquivalence orbit).val] 7).toNat
      rw [hrow]
      simp [dataEntry, Array.getD_eq_getD_getElem?, hindex,
        orbitEntry]
    _ = 425 * 425 := hsum



theorem orbitPairKey_mem_representative_orbit
    (pair : Fin 425 × Fin 425) :
    pair ∈ MulAction.orbit OrbitSignedSymmetry
      (orbitGramRepresentative (orbitPairKey pair.1 pair.2)) :=
  orbitPair_mem_representative_orbit pair.1 pair.2



theorem orbitPairKey_eq_iff_mem_representative_orbit
    (pair : Fin 425 × Fin 425) (orbit : Fin 2256) :
    orbitPairKey pair.1 pair.2 = orbit ↔
      pair ∈ MulAction.orbit OrbitSignedSymmetry
        (orbitGramRepresentative orbit) :=
  orbitLabel_eq_iff_mem_of_card
    orbitGramRepresentative
    (fun pair : Fin 425 × Fin 425 => orbitPairKey pair.1 pair.2)
    orbitPairKey_mem_representative_orbit
    orbitGramRepresentative_orbit_card_sum pair orbit


theorem orbitPair_bucket_iff (orbit : Fin 2256)
    (pair : Fin 425 × Fin 425) :
    orbitPairKey pair.1 pair.2 = orbit ↔
      pair ∈ MulAction.orbit OrbitSignedSymmetry
        (orbitGramRepresentative orbit) :=
  orbitPairKey_eq_iff_mem_representative_orbit pair orbit



theorem orbitPairKey_swap (left right : Fin 425) :
    orbitPairKey right left = orbitPairKey left right :=
  orbitPairLabel_swap_eq_of_card orbitGramRepresentative
    (fun pair : Fin 425 × Fin 425 => orbitPairKey pair.1 pair.2)
    orbitPairKey_mem_representative_orbit
    orbitGramRepresentative_orbit_card_sum left right



theorem orbitPairKey_symmetry (symmetry : OrbitSymmetry)
    (left right : Fin 425) :
    orbitPairKey (symmetry • left) (symmetry • right) =
      orbitPairKey left right :=
  orbitPairLabel_symmetry_eq_of_card orbitGramRepresentative
    (fun pair : Fin 425 × Fin 425 => orbitPairKey pair.1 pair.2)
    orbitPairKey_mem_representative_orbit
    orbitGramRepresentative_orbit_card_sum symmetry left right


theorem gramEntry_swap (left right : Fin 425) :
    gramEntry right.val left.val = gramEntry left.val right.val := by
  unfold gramEntry
  change gramOrbitCoefficient (orbitPairKey right left).val =
    gramOrbitCoefficient (orbitPairKey left right).val
  rw [orbitPairKey_swap]



theorem gramEntry_symmetry (symmetry : OrbitSymmetry)
    (left right : Fin 425) :
    gramEntry (symmetry • left).val (symmetry • right).val =
      gramEntry left.val right.val := by
  unfold gramEntry
  change
    gramOrbitCoefficient
        (orbitPairKey (symmetry • left) (symmetry • right)).val =
      gramOrbitCoefficient (orbitPairKey left right).val
  rw [orbitPairKey_symmetry]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

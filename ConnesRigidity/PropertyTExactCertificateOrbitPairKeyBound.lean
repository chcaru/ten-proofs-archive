


import ConnesRigidity.PropertyTExactCertificateOrbitBasisPermutation
import ConnesRigidity.PropertyTExactCertificateOrbitPairWitnessSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitTransportValidation









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



theorem orbitBasisTransportIndices_lt (index : Fin 425) :
    basisOrbit index.val < 26 ∧ basisTransportSymmetry index.val < 64 := by
  have hcheck := orbitBasisTransportCheck_sound orbitBasisTransportCheck_valid
  have hindex : index.val < basisTransporterData.size := by
    rw [hcheck.1, orbitBasisData_size]
    exact index.isLt
  have hrow : basisTransporterData[index.val]? =
      some basisTransporterData[index.val] := by
    simp [hindex]
  have hvalid := orbitBasisTransportRowCheck_sound index.val
    basisTransporterData[index.val] hrow (hcheck.2 index.val hindex)
  have horbit : basisOrbit index.val =
      (orbitEntry basisTransporterData[index.val] 0).toNat := by
    simp [basisOrbit, dataEntry, Array.getD_eq_getD_getElem?,
      orbitEntry, hindex]
  have hsymmetry : basisTransportSymmetry index.val =
      (orbitEntry basisTransporterData[index.val] 1).toNat := by
    simp [basisTransportSymmetry, dataEntry,
      Array.getD_eq_getD_getElem?, orbitEntry, hindex]
  constructor
  · rw [horbit]
    exact (Int.toNat_lt hvalid.2.1.1).mpr
      (by simpa [pairWitnessDataSizes_valid.2.2.2.2.1] using
        hvalid.2.1.2)
  · rw [hsymmetry]
    exact (Int.toNat_lt hvalid.2.2.1.1).mpr
      (by simpa [pairWitnessDataSizes_valid.2.2.1] using
        hvalid.2.2.1.2)


theorem orbitInverseSymmetry_lt (symmetry : Nat) (hsymmetry : symmetry < 64) :
    inverseSymmetry symmetry < 64 := by
  have hcheck := orbitSymmetryInverseCheck_sound orbitSymmetryInverseCheck_valid
  have hsize : symmetryInverseData.size = 64 := by
    rw [hcheck.1, pairWitnessDataSizes_valid.2.2.1]
  have hindex : symmetry < symmetryInverseData.size := by
    simpa [hsize] using hsymmetry
  have hrow : symmetryInverseData[symmetry]? =
      some symmetryInverseData[symmetry] := by
    simp [hindex]
  have hvalid := hcheck.2 symmetry hindex
  simp only [orbitSymmetryInverseRowCheck, hrow, Bool.and_eq_true,
    decide_eq_true_eq] at hvalid
  have hinverse := orbitIndexCheck_sound
    (orbitEntry symmetryInverseData[symmetry] 0)
    symmetryData.size hvalid.1.2
  have hvalue : inverseSymmetry symmetry =
      (orbitEntry symmetryInverseData[symmetry] 0).toNat := by
    simp [inverseSymmetry, dataEntry,
      Array.getD_eq_getD_getElem?, orbitEntry, hindex]
  rw [hvalue]
  exact (Int.toNat_lt hinverse.1).mpr
    (by simpa [pairWitnessDataSizes_valid.2.2.1] using hinverse.2)


theorem normalizedPairRight_lt (left right : Fin 425) :
    normalizedPairRight left.val right.val < 425 := by
  have hsymmetry := orbitInverseSymmetry_lt
    (basisTransportSymmetry left.val)
    (orbitBasisTransportIndices_lt left).2
  exact symmetryBasisImage_lt ⟨_, hsymmetry⟩ right



theorem orbitPair_lt (left right : Fin 425) :
    pairOrbit left.val right.val < 2256 := by
  have horbit := (orbitBasisTransportIndices_lt left).1
  have hsecond := normalizedPairRight_lt left right
  have hentry := orbitPairWitnessEntryCheck_sound
    (basisOrbit left.val) (normalizedPairRight left.val right.val)
    (orbitPairWitnessEntryCheck_valid
      (basisOrbit left.val) (normalizedPairRight left.val right.val)
      (by simpa [pairWitnessDataSizes_valid.2.2.2.2.1] using horbit)
      (by simpa [pairWitnessDataSizes_valid.1] using hsecond))
  unfold pairOrbit
  exact (Int.toNat_lt hentry.2.2.1.1).mpr
    (by simpa [pairWitnessDataSizes_valid.2.1] using hentry.2.2.1.2)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

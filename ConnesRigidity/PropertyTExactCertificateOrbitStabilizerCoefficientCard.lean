


import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerCoefficientSoundness










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0



theorem orbitCoefficientRepresentative_orbit_card (coefficient : Fin 995) :
    Fintype.card (MulAction.orbit OrbitSignedSymmetry
      (coefficientRepresentativeElement coefficient.val)) =
        (dataEntry coefficientOrbitSizeData coefficient.val 0).toNat := by
  classical
  let rows := coefficientRepresentativeData.toList
  let inverses := coefficientInverseRepresentativeData.toList
  let sizes := coefficientOrbitSizeData.toList
  let permutations := orbitPermutationRepresentatives symmetryData.toList
  have hindex : coefficient.val < rows.length := by
    simp [rows, coefficientRepresentativeData_size]
  have hchecked := orbitCoefficientMaskStabilizerRowsCheck_valid
  have hlengths := orbitCoefficientMaskStabilizerRowsCheck_lengths
    permutations rows inverses sizes hchecked
  obtain ⟨hinverse, hsize, hequation⟩ :=
    orbitCoefficientMaskStabilizerRowsCheck_get
      permutations rows inverses sizes coefficient.val hindex hchecked
  have hrowIndex : coefficient.val < coefficientRepresentativeData.size := by
    simpa [rows] using hindex
  have hrow : rows[coefficient.val] =
      coefficientRepresentativeData.getD coefficient.val #[] := by
    simp [rows, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hrowIndex]
  have hsizeIndex : coefficient.val < coefficientOrbitSizeData.size := by
    simpa [sizes] using hsize
  have hsizeEntry : orbitEntry sizes[coefficient.val] 0 =
      dataEntry coefficientOrbitSizeData coefficient.val 0 := by
    simp [sizes, dataEntry, orbitEntry, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hsizeIndex]
  have hpositive : 0 < dataEntry coefficientOrbitSizeData coefficient.val 0 := by
    rw [← packedCoefficientOrbitSize_eq_dataEntry coefficient.val hsizeIndex]
    unfold packedCoefficientOrbitSize
    exact_mod_cast Nat.pow_pos (by decide : 0 < (2 : Nat))
  have hvalid := orbitCoefficientInverseRowsCheck_get
    rows inverses coefficient.val hindex hlengths.1
      orbitCoefficientInverseRowsCheck_valid
  have htransport := orbitCoefficientMaskStabilizerCount_eq_transport
    symmetryData.toList rows[coefficient.val] inverses[coefficient.val]
      orbitSymmetryGroupAlignmentCheck_valid
  have hcard := orbitCoefficientTransportStabilizerCountAux_eq_card
    rows[coefficient.val] inverses[coefficient.val] hvalid.1 hvalid.2
  have hstabilizer :
      Fintype.card
          (MulAction.stabilizer OrbitSignedSymmetry
            (coefficientRepresentativeElement coefficient.val)) =
        orbitCoefficientMaskStabilizerCount
          permutations rows[coefficient.val] inverses[coefficient.val] := by
    rw [coefficientRepresentativeElement, ← hrow]
    exact hcard.symm.trans htransport.symm
  apply signedOrbit_card_eq_checked_size
    (coefficientRepresentativeElement coefficient.val)
    (dataEntry coefficientOrbitSizeData coefficient.val 0)
    (orbitCoefficientMaskStabilizerCount
      permutations rows[coefficient.val] inverses[coefficient.val])
    hpositive hstabilizer
  simpa [hsizeEntry] using hequation

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

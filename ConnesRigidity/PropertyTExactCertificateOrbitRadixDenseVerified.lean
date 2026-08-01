


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseValidation
import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseCacheLookup
import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseRowMetadata
import ConnesRigidity.PropertyTExactCertificateOrbitRadixNormalizedVerified
import ConnesRigidity.PropertyTExactCertificateOrbitSymmetryWordInduction











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000


theorem orbitRadixBasisPermutationData_size :
    basisPermutationData.size = 64 := by
  have hshape :=
    (orbitBasisPermutationCheck_sound orbitBasisPermutationCheck_valid).1
  have hsymmetry :=
    (orbitSymmetryCompositionCheck_sound
      orbitSymmetryCompositionCheck_valid).1
  simpa [symmetryCardinality] using hshape.trans hsymmetry




theorem orbitRadixDenseReducedGramEntry_eq
    (row column : Fin 424) :
    (radixDenseReducedGramRowData.getD row.val []).getD (column.val + 1) 0 =
      gramEntry (row.val + 1) (column.val + 1) := by
  obtain ⟨stored, entries, transporter, packedOrbit, packed,
    hdense, htransport, hpacked, _hstored, hlength, horbit,
    _hsymmetry, hinverse, _hpackedOrbit, hentries⟩ :=
    orbitRadixDenseGramRow_metadata row
  let orbit := (transporter.getD 0 0).toNat
  let symmetry := (transporter.getD 1 0).toNat
  let inverse := inverseSymmetry symmetry
  have hcolumn : column.val < entries.length := by
    simp [hlength]
  have hentry := orbitRadixDenseGramEntriesCheck_get
    packed (pairWitnessPackedPermutationRows.getD inverse 0)
      entries 0 column.val hcolumn (by simpa [inverse, symmetry] using hentries)
  have hcolumnFull : column.val + 1 < 425 := by omega
  have hinverse' : inverse < 64 := by
    simpa [inverse, symmetry] using hinverse
  have hinverseArray : inverse < basisPermutationData.size := by
    simpa [orbitRadixBasisPermutationData_size] using hinverse'
  have himage :=
    pairWitnessPackedImage_eq_symmetryBasisImage
      inverse (column.val + 1) hinverseArray hcolumnFull
  have hnormalized :
      symmetryBasisImage inverse (column.val + 1) < 425 :=
    symmetryBasisImage_lt ⟨inverse, hinverse'⟩
      ⟨column.val + 1, hcolumnFull⟩
  have hactual :=
    orbitRadixPackedNormalizedGramValue_eq_gramOrbitCoefficient
      orbit (symmetryBasisImage inverse (column.val + 1))
      (by simpa [orbit] using horbit) hnormalized
  have hpackedValue :=
    orbitRadixPackedNormalizedGram_get orbit packedOrbit packed
      (by simpa [orbit] using hpacked)
  have hcache := orbitRadixDenseReducedGram_get
    row.val column.val stored entries hdense hcolumn
  rw [hcache, hentry]
  simp only [Nat.zero_add]
  change orbitRadixPackedSignedValue packed
      (pairWitnessPackedImage inverse (column.val + 1)) = _
  rw [himage, ← hpackedValue, hactual]
  unfold gramEntry pairOrbit normalizedPairRight
    basisOrbit basisTransportSymmetry
  simp [dataEntry, Array.getD_eq_getD_getElem?,
    htransport, orbit, symmetry, inverse]



theorem orbitRadixDenseReducedGramRow_eq (row : Fin 424) :
    (radixDenseReducedGramRowData.getD row.val []).drop 1 =
      (List.range 424).map fun column =>
        gramEntry (row.val + 1) (column + 1) := by
  obtain ⟨stored, entries, _transporter, _packedOrbit, _packed,
    hdense, _htransport, _hpacked, _hstored, hlength, _⟩ :=
    orbitRadixDenseGramRow_metadata row
  have hdata : radixDenseReducedGramRowData.getD row.val [] =
      stored :: entries :=
    orbitRadixDenseReducedGramRow_get row.val stored entries hdense
  rw [hdata]
  simp only [List.drop_succ_cons, List.drop_zero]
  apply List.ext_getElem
  · simp [hlength]
  · intro column hleft hright
    have hcolumn : column < 424 := by simpa [hlength] using hleft
    have hentry := orbitRadixDenseReducedGramEntry_eq
      row ⟨column, hcolumn⟩
    have hcache := orbitRadixDenseReducedGram_get
      row.val column stored entries hdense hleft
    simpa using hcache.symm.trans hentry

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

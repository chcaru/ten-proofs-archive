
import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseRowMetadata

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

theorem orbitRadixDenseReducedGramRow_shape (row : Fin 424) :
    ∃ stored entries,
      radixDenseReducedGramRowData[row.val]? = some (stored :: entries) ∧
        entries.length = 424 := by
  obtain ⟨stored, entries, _transporter, _packedOrbit, _packed,
    hrow, _htransporter, _hpacked, _hstored, hlength, _⟩ :=
    orbitRadixDenseGramRow_metadata row
  exact ⟨stored, entries, hrow, hlength⟩

theorem orbitRadixDenseReducedGramRow_length (row : Fin 424) :
    ((radixDenseReducedGramRowData.getD row.val []).drop 1).length = 424 := by
  obtain ⟨stored, entries, hrow, hlength⟩ :=
    orbitRadixDenseReducedGramRow_shape row
  simpa [List.getD_eq_getElem?_getD, hrow] using hlength

end ConnesRigidity.AffineSymplecticOrbitCertificate

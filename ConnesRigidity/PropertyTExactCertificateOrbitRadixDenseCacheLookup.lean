
import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

theorem orbitRadixPackedNormalizedGram_get
    (orbit : Nat) (header packed : Int)
    (hrow : radixPackedNormalizedGramRowData[orbit]? =
      some [header, packed]) :
    (radixPackedNormalizedGramRowData.getD orbit []).getD 1 0 = packed := by
  change
    ((radixPackedNormalizedGramRowData[orbit]?).getD []).getD 1 0 = packed
  rw [hrow]
  rfl

theorem orbitRadixDenseReducedGramRow_get
    (row : Nat) (header : Int) (entries : List Int)
    (hrow : radixDenseReducedGramRowData[row]? =
      some (header :: entries)) :
    radixDenseReducedGramRowData.getD row [] = header :: entries := by
  rw [List.getD_eq_getElem?_getD, hrow]
  rfl

theorem orbitRadixDenseReducedGram_get
    (row column : Nat) (header : Int) (entries : List Int)
    (hrow : radixDenseReducedGramRowData[row]? =
      some (header :: entries))
    (hcolumn : column < entries.length) :
    (radixDenseReducedGramRowData.getD row []).getD (column + 1) 0 =
      entries[column] := by
  rw [orbitRadixDenseReducedGramRow_get row header entries hrow]
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hcolumn]

end ConnesRigidity.AffineSymplecticOrbitCertificate

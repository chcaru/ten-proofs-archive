
import ConnesRigidity.PropertyTExactCertificateOrbitData

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

def scaledInverseDecodePairs : List Int → List (Int × Int)
  | column :: value :: remaining =>
      (column, value) :: scaledInverseDecodePairs remaining
  | _ => []

noncomputable def scaledInverseSparsePairs (row : Nat) : List (Int × Int) :=
  scaledInverseDecodePairs ((scaledInverseRowData.getD row []).drop 1)

def scaledInversePairLookup (column : Int) : List Int → Int
  | key :: value :: remaining =>
      if key = column then value
      else scaledInversePairLookup column remaining
  | _ => 0

noncomputable def scaledCongruenceInverseEntry
    (row column : Nat) : Int :=
  scaledInversePairLookup (column : Int)
    ((scaledInverseRowData.getD row []).drop 1)

noncomputable abbrev scaledInverseEntryInt
    (row column : Nat) : Int :=
  scaledCongruenceInverseEntry row column

end ConnesRigidity.AffineSymplecticOrbitCertificate

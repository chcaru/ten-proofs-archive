


import ConnesRigidity.PropertyTExactCertificateData





namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

noncomputable section


def productIndexEntryIsValid
    (left : Array ℤ) (index : ℤ) (right : Array ℤ) : Bool :=
  let k := index.toNat
  decide (k < 73033) &&
    rawAffineProductMatchesArray left (allElementDataRow k) right


def productIndexEntriesAreValid
    (left : Array ℤ) :
    List ℤ → List (Array ℤ) → Bool
  | [], [] => true
  | index :: indices, right :: rights =>
      productIndexEntryIsValid left index right &&
        productIndexEntriesAreValid left indices rights
  | _, _ => false


def productIndexRowIsValid (i : ℕ) : Bool :=
  let indices := productIndexDataRow i
  decide (indices.size = 425) &&
    productIndexEntriesAreValid
      (basisDataArray.getD i #[])
      indices.toList basisDataArray.toList

end

end AffineSymplecticCertificate

end ConnesRigidity

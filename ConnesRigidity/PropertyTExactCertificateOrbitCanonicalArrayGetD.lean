
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalData
import Mathlib.Data.List.GetD

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

theorem coefficientCanonical_toArray_getD
    (rows : List (List Int)) (index : Nat) :
    rows.toArray.getD index [] = rows.getD index [] := by
  by_cases hindex : index < rows.length
  · simp [Array.getD, List.getD_eq_getElem?_getD, hindex]
  · simp [Array.getD, List.getD_eq_getElem?_getD, hindex]

end ConnesRigidity.AffineSymplecticOrbitCertificate

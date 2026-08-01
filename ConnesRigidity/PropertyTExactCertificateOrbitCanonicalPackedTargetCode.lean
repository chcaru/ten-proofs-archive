
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedCoordinate
import ConnesRigidity.PropertyTExactCertificateOrbitTargetRadix

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

theorem canonicalPackedRowList_eq_targetCoordinateCode
    (coordinates : List Int)
    (hbound : targetCoordinateBounds coordinates = true) :
    ((canonicalPackedRowList coordinates : Nat) : Int) =
      targetCoordinateCode coordinates := by
  induction coordinates with
  | nil => rfl
  | cons coordinate coordinates ih =>
      have hbounds := (targetCoordinateBounds_cons
        coordinate coordinates).mp hbound
      have hnonnegative : 0 ≤ coordinate + 8 := by
        omega
      have htail := ih hbounds.2.2
      simp only [canonicalPackedRowList, targetCoordinateCode,
        canonicalPackedCoordinateDigit]
      omega

theorem canonicalPackedRow_eq_targetCoordinateCode
    (row : Array Int)
    (hbound : targetCoordinateBounds row.toList = true) :
    ((canonicalPackedRow row : Nat) : Int) =
      targetCoordinateCode row.toList := by
  exact canonicalPackedRowList_eq_targetCoordinateCode
    row.toList hbound

end ConnesRigidity.AffineSymplecticOrbitCertificate

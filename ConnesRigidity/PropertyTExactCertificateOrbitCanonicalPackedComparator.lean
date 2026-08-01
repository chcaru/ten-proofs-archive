


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalLazyLex
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedAction
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedCoordinate










namespace ConnesRigidity.AffineSymplecticOrbitCertificate



def canonicalPackedCoordinateLE
    (canonicalPacked actionCode sourcePacked : Nat) : Nat → Bool
  | 0 => true
  | remaining + 1 =>
      let index := remaining
      let left := canonicalPackedCoordinate canonicalPacked index
      let right := canonicalPackedActionCoordinate actionCode sourcePacked index
      if left < right then true
      else if right < left then false
      else canonicalPackedCoordinateLE canonicalPacked actionCode sourcePacked
        remaining





theorem canonicalPackedCoordinateLE_eq_lazy
    (canonicalPacked actionCode sourcePacked : Nat)
    (canonicalSymmetry canonicalSource symmetry row : Array Int)
    (count : Nat) (hcount : count ≤ 20)
    (hcanonical : ∀ index, index < 20 →
      canonicalPackedCoordinate canonicalPacked index =
        signedAffineCoordinate canonicalSymmetry canonicalSource index)
    (haction : ∀ index, index < 20 →
      canonicalPackedActionCoordinate actionCode sourcePacked index =
        signedAffineCoordinate symmetry row index) :
    canonicalPackedCoordinateLE canonicalPacked actionCode sourcePacked count =
      canonicalLazyCoordinateLE canonicalSymmetry canonicalSource
        symmetry row count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hindex : count < 20 := by omega
      simp only [canonicalPackedCoordinateLE, canonicalLazyCoordinateLE,
        hcanonical count hindex, haction count hindex]
      rw [ih (by omega)]



theorem canonicalPackedCoordinateLE_sound
    (canonicalPacked actionCode sourcePacked : Nat)
    (canonicalSymmetry canonicalSource symmetry row : Array Int)
    (hcanonical : ∀ index, index < 20 →
      canonicalPackedCoordinate canonicalPacked index =
        signedAffineCoordinate canonicalSymmetry canonicalSource index)
    (haction : ∀ index, index < 20 →
      canonicalPackedActionCoordinate actionCode sourcePacked index =
        signedAffineCoordinate symmetry row index)
    (hcheck : canonicalPackedCoordinateLE canonicalPacked actionCode
      sourcePacked 20 = true) :
    (signedRowAction canonicalSymmetry canonicalSource).toList.reverse ≤
      signedAffineDescendingCoordinates symmetry row := by
  apply canonicalLazyCoordinateLE_sound
    canonicalSymmetry canonicalSource symmetry row
  rw [← canonicalPackedCoordinateLE_eq_lazy
    canonicalPacked actionCode sourcePacked canonicalSymmetry canonicalSource
    symmetry row 20 (by omega) hcanonical haction]
  exact hcheck

end ConnesRigidity.AffineSymplecticOrbitCertificate

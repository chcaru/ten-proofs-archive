
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalFastLex

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

theorem signedAffineCoordinate_eq_signedRowAction_getD
    (symmetry row : Array Int) (index : Nat) (hindex : index < 20) :
    signedAffineCoordinate symmetry row index =
      (signedRowAction symmetry row).getD index 0 := by
  simp [signedRowAction, signedAffineCoordinate, getElem?_pos,
    hindex]

def canonicalLazyCoordinateLE
    (canonicalSymmetry canonicalSource symmetry row : Array Int) :
    Nat → Bool
  | 0 => true
  | remaining + 1 =>
      let index := remaining
      let left := signedAffineCoordinate canonicalSymmetry canonicalSource index
      let right := signedAffineCoordinate symmetry row index
      if left < right then true
      else if right < left then false
      else canonicalLazyCoordinateLE canonicalSymmetry canonicalSource
        symmetry row remaining

theorem canonicalLazyCoordinateLE_eq
    (canonicalSymmetry canonicalSource symmetry row : Array Int)
    (count : Nat) (hcount : count ≤ 20) :
    canonicalLazyCoordinateLE canonicalSymmetry canonicalSource
      symmetry row count =
        canonicalCoordinateLE (signedRowAction canonicalSymmetry canonicalSource)
          symmetry row count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hindex : count < 20 := by omega
      simp only [canonicalLazyCoordinateLE, canonicalCoordinateLE,
        ← signedAffineCoordinate_eq_signedRowAction_getD
          canonicalSymmetry canonicalSource count hindex]
      rw [ih (by omega)]

theorem canonicalLazyCoordinateLE_sound
    (canonicalSymmetry canonicalSource symmetry row : Array Int)
    (hcheck : canonicalLazyCoordinateLE canonicalSymmetry canonicalSource
      symmetry row 20 = true) :
    (signedRowAction canonicalSymmetry canonicalSource).toList.reverse ≤
      signedAffineDescendingCoordinates symmetry row := by
  apply (canonicalCoordinateLE_true_iff
    (signedRowAction canonicalSymmetry canonicalSource)
    symmetry row (by simp [signedRowAction])).mp
  rw [← canonicalLazyCoordinateLE_eq
    canonicalSymmetry canonicalSource symmetry row 20 (by omega)]
  exact hcheck

end ConnesRigidity.AffineSymplecticOrbitCertificate

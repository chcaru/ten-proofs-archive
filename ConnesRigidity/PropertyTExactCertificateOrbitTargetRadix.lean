
import ConnesRigidity.PropertyTExactCertificateOrbitTargetData

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

def targetCoordinateCode : List Int → Int
  | [] => 0
  | coordinate :: coordinates =>
      coordinate + 8 + 16 * targetCoordinateCode coordinates

def targetCoordinateBounds (coordinates : List Int) : Bool :=
  coordinates.all fun coordinate =>
    decide (-8 ≤ coordinate) && decide (coordinate < 8)

@[simp]
theorem targetCoordinateBounds_nil :
    targetCoordinateBounds [] = true := rfl

@[simp]
theorem targetCoordinateBounds_cons
    (coordinate : Int) (coordinates : List Int) :
    targetCoordinateBounds (coordinate :: coordinates) = true ↔
      -8 ≤ coordinate ∧ coordinate < 8 ∧
        targetCoordinateBounds coordinates = true := by
  simp [targetCoordinateBounds, Bool.and_eq_true, and_assoc]

theorem targetCoordinateCode_injective
    {left right : List Int}
    (hlength : left.length = right.length)
    (hleft : targetCoordinateBounds left = true)
    (hright : targetCoordinateBounds right = true)
    (hcode : targetCoordinateCode left = targetCoordinateCode right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons coordinate coordinates => simp at hlength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at hlength
      | cons rightHead rightTail =>
          have hlengthTail : leftTail.length = rightTail.length := by
            simpa using hlength
          have hleftBounds :=
            (targetCoordinateBounds_cons leftHead leftTail).mp hleft
          have hrightBounds :=
            (targetCoordinateBounds_cons rightHead rightTail).mp hright
          change
            leftHead + 8 + 16 * targetCoordinateCode leftTail =
              rightHead + 8 + 16 * targetCoordinateCode rightTail at hcode
          have hheads : leftHead = rightHead := by
            omega
          subst rightHead
          have htailsCode :
              targetCoordinateCode leftTail =
                targetCoordinateCode rightTail := by
            omega
          have htails := inductionHypothesis hlengthTail
            hleftBounds.2.2 hrightBounds.2.2 htailsCode
          rw [htails]

end ConnesRigidity.AffineSymplecticOrbitCertificate

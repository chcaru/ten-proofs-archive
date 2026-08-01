


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalFastLex









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



def coefficientCanonicalWitnessRowFastCheck
    (orbit : Nat) (symmetries : List (Array Int))
    (witness : List Int) (representative inverse : Array Int) : Bool :=
  let index := witness.getD 2 0
  let inversion := witness.getD 3 0
  let source := if inversion = 0 then representative else inverse
  let symmetry := symmetryData.getD index.toNat #[]
  let canonical := signedRowAction symmetry source
  decide (witness.length = 4) &&
    decide (witness.getD 0 0 = (orbit : Int)) &&
    decide (0 ≤ index ∧ index < (64 : Int)) &&
    decide (inversion = 0 ∨ inversion = 1) &&
    decide (representative.size = 20) &&
    decide (inverse.size = 20) &&
    decide
      (targetCoordinateCode canonical.toList = witness.getD 1 0) &&
    coefficientCanonicalImagesFastCheck canonical representative inverse
      symmetries

theorem coefficientCanonicalWitnessRowFastCheck_sound
    (orbit : Nat) (symmetries : List (Array Int))
    (witness : List Int) (representative inverse : Array Int)
    (hcheck : coefficientCanonicalWitnessRowFastCheck orbit symmetries
      witness representative inverse = true) :
    coefficientCanonicalWitnessRowCheck orbit symmetries
      witness representative inverse = true := by
  unfold coefficientCanonicalWitnessRowFastCheck at hcheck
  unfold coefficientCanonicalWitnessRowCheck
  dsimp at hcheck ⊢
  simp only [Bool.and_eq_true] at hcheck ⊢
  refine ⟨hcheck.1, ?_⟩
  apply coefficientCanonicalImagesFastCheck_sound
  · simp [signedRowAction]
  · exact hcheck.2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

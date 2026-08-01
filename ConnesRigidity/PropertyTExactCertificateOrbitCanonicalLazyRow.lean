


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalLazyLex









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



def coefficientCanonicalImagesLazyCheck
    (canonicalSymmetry canonicalSource representative inverse : Array Int)
    (symmetries : List (Array Int)) : Bool :=
  symmetries.all fun symmetry =>
    canonicalLazyCoordinateLE canonicalSymmetry canonicalSource
      symmetry representative 20 &&
    canonicalLazyCoordinateLE canonicalSymmetry canonicalSource
      symmetry inverse 20



theorem coefficientCanonicalImagesLazyCheck_sound
    (canonicalSymmetry canonicalSource representative inverse : Array Int)
    (symmetries : List (Array Int))
    (hcheck : coefficientCanonicalImagesLazyCheck canonicalSymmetry
      canonicalSource representative inverse symmetries = true) :
    coefficientCanonicalImagesCheck
      (signedRowAction canonicalSymmetry canonicalSource)
      representative inverse symmetries = true := by
  unfold coefficientCanonicalImagesLazyCheck at hcheck
  unfold coefficientCanonicalImagesCheck
  apply List.all_eq_true.mpr
  intro symmetry hsymmetry
  have hrow := (List.all_eq_true.mp hcheck) symmetry hsymmetry
  simp only [Bool.and_eq_true] at hrow ⊢
  constructor
  · exact decide_eq_true
      (canonicalLazyCoordinateLE_sound
        canonicalSymmetry canonicalSource symmetry representative hrow.1)
  · exact decide_eq_true
      (canonicalLazyCoordinateLE_sound
        canonicalSymmetry canonicalSource symmetry inverse hrow.2)



def coefficientCanonicalWitnessRowLazyCheck
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
    coefficientCanonicalImagesLazyCheck symmetry source
      representative inverse symmetries



theorem coefficientCanonicalWitnessRowLazyCheck_sound
    (orbit : Nat) (symmetries : List (Array Int))
    (witness : List Int) (representative inverse : Array Int)
    (hcheck : coefficientCanonicalWitnessRowLazyCheck orbit symmetries
      witness representative inverse = true) :
    coefficientCanonicalWitnessRowCheck orbit symmetries
      witness representative inverse = true := by
  unfold coefficientCanonicalWitnessRowLazyCheck at hcheck
  unfold coefficientCanonicalWitnessRowCheck
  dsimp at hcheck ⊢
  simp only [Bool.and_eq_true] at hcheck ⊢
  refine ⟨hcheck.1, ?_⟩
  exact coefficientCanonicalImagesLazyCheck_sound _ _ _ _ _ hcheck.2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

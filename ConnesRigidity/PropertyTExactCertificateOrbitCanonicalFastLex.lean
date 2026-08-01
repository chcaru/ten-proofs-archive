


import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientOrbitDisjointness











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



def canonicalCoordinateLE
    (canonical symmetry row : Array Int) : Nat → Bool
  | 0 => true
  | remaining + 1 =>
      let index := remaining
      let left := canonical.getD index 0
      let right := signedAffineCoordinate symmetry row index
      if left < right then true
      else if right < left then false
      else canonicalCoordinateLE canonical symmetry row remaining



private theorem canonicalList_cons_le_cons_iff
    {first second : Int} {left right : List Int} :
    first :: left ≤ second :: right ↔
      first < second ∨ first = second ∧ left ≤ right := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  constructor
  · rintro (h | h)
    · change List.Lex (· < ·) (first :: left) (second :: right) at h
      cases h with
      | rel h => exact Or.inl h
      | cons h => exact Or.inr ⟨rfl, Or.inl h⟩
    · exact Or.inr
        ⟨(List.cons.inj h).1, Or.inr ((List.cons.inj h).2)⟩
  · rintro (h | ⟨h, htail⟩)
    · exact Or.inl (List.Lex.rel h)
    · subst second
      rcases htail with htail | htail
      · exact Or.inl (List.Lex.cons htail)
      · exact Or.inr (congrArg (List.cons first) htail)



theorem canonicalCoordinateLE_true_iff_range
    (canonical symmetry row : Array Int) (count : Nat) :
    canonicalCoordinateLE canonical symmetry row count = true ↔
      ((List.range count).reverse.map fun index =>
        canonical.getD index 0) ≤
        ((List.range count).reverse.map fun index =>
          signedAffineCoordinate symmetry row index) := by
  induction count with
  | zero => simp [canonicalCoordinateLE]
  | succ count ih =>
      have hrange :
          (List.range (count + 1)).reverse =
            count :: (List.range count).reverse := by
        simp [List.range_succ, List.reverse_append]
      rw [hrange]
      simp only [List.map_cons]
      rw [canonicalList_cons_le_cons_iff]
      simp only [canonicalCoordinateLE]
      by_cases hleft :
          canonical.getD count 0 < signedAffineCoordinate symmetry row count
      · simp only [hleft, ↓reduceIte, true_or]
      · by_cases hright :
            signedAffineCoordinate symmetry row count < canonical.getD count 0
        · have hne :
              canonical.getD count 0 ≠
                signedAffineCoordinate symmetry row count := by omega
          simp only [hleft, hright, hne, ↓reduceIte,
            false_and, or_self, Bool.false_eq_true]
        · have hequal :
              canonical.getD count 0 =
                signedAffineCoordinate symmetry row count := by omega
          simp only [↓reduceIte, hequal,
            lt_self_iff_false, false_or, true_and, ih]



theorem canonicalCoordinateLE_true_iff
    (canonical symmetry row : Array Int)
    (hwidth : canonical.size = 20) :
    canonicalCoordinateLE canonical symmetry row 20 = true ↔
      canonical.toList.reverse ≤
        signedAffineDescendingCoordinates symmetry row := by
  rw [canonicalCoordinateLE_true_iff_range]
  unfold signedAffineDescendingCoordinates
  have hcoordinates :
      (List.range 20).map (fun index => canonical.getD index 0) =
        canonical.toList := by
    apply List.ext_getElem
    · simp [hwidth]
    · intro index hleft hright
      have hindex : index < canonical.size := by
        simpa [hwidth] using hleft
      simp [getElem?_pos canonical index hindex]
  have hdescending :
      (List.range 20).reverse.map
          (fun index => canonical.getD index 0) =
        canonical.toList.reverse := by
    simpa only [List.map_reverse] using congrArg List.reverse hcoordinates
  rw [hdescending]



def coefficientCanonicalImagesFastCheck
    (canonical representative inverse : Array Int)
    (symmetries : List (Array Int)) : Bool :=
  symmetries.all fun symmetry =>
    canonicalCoordinateLE canonical symmetry representative 20 &&
      canonicalCoordinateLE canonical symmetry inverse 20



theorem coefficientCanonicalImagesFastCheck_sound
    (canonical representative inverse : Array Int)
    (symmetries : List (Array Int))
    (hwidth : canonical.size = 20)
    (hcheck : coefficientCanonicalImagesFastCheck canonical representative
      inverse symmetries = true) :
    coefficientCanonicalImagesCheck canonical representative inverse
      symmetries = true := by
  unfold coefficientCanonicalImagesFastCheck at hcheck
  unfold coefficientCanonicalImagesCheck
  apply List.all_eq_true.mpr
  intro symmetry hsymmetry
  have hrow := (List.all_eq_true.mp hcheck) symmetry hsymmetry
  simp only [Bool.and_eq_true] at hrow ⊢
  constructor
  · exact decide_eq_true
      ((canonicalCoordinateLE_true_iff
        canonical symmetry representative hwidth).mp hrow.1)
  · exact decide_eq_true
      ((canonicalCoordinateLE_true_iff
        canonical symmetry inverse hwidth).mp hrow.2)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

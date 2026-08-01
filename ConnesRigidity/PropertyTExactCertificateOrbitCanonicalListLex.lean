


import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientOrbitDisjointness









namespace ConnesRigidity.AffineSymplecticOrbitCertificate



theorem canonicalListCons_le_cons_iff {α : Type*} [LinearOrder α]
    (a b : α) (left right : List α) :
    a :: left ≤ b :: right ↔ a < b ∨ a = b ∧ left ≤ right := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  constructor
  · rintro (h | h)
    · change List.Lex (· < ·) (a :: left) (b :: right) at h
      cases h with
      | rel h => exact Or.inl h
      | cons h => exact Or.inr ⟨rfl, Or.inl h⟩
    · exact Or.inr
        ⟨(List.cons.inj h).1, Or.inr ((List.cons.inj h).2)⟩
  · rintro (h | ⟨h, htail⟩)
    · exact Or.inl (List.Lex.rel h)
    · subst b
      rcases htail with htail | htail
      · exact Or.inl (List.Lex.cons htail)
      · exact Or.inr (congrArg (List.cons a) htail)


theorem canonicalList_cons_le_cons_iff {a b : Int}
    {left right : List Int} :
    a :: left ≤ b :: right ↔ a < b ∨ a = b ∧ left ≤ right :=
  canonicalListCons_le_cons_iff a b left right

end ConnesRigidity.AffineSymplecticOrbitCertificate

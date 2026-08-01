


import ConnesRigidity.PropertyTExactCertificateOrbitAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitGroupRing










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

universe u v w

variable {G : Type u} [Group G]



@[simp] theorem groupRingMap_coeff_image
    (symmetry : G ≃* G) (value : RationalGroupRing G) (g : G) :
    (groupRingMap symmetry value).coeff (symmetry g) = value.coeff g := by
  change
    ((MonoidAlgebra.mapDomainRingEquiv ℚ symmetry) value).coeff
      (symmetry g) = value.coeff g
  rw [MonoidAlgebra.coeff_mapDomainRingEquiv,
    Finsupp.equivMapDomain_apply]
  simp



theorem coeff_image_eq_of_groupRingMap_fixed
    (symmetry : G ≃* G) (value : RationalGroupRing G)
    (hfixed : groupRingMap symmetry value = value) (g : G) :
    value.coeff (symmetry g) = value.coeff g := by
  calc
    value.coeff (symmetry g) =
        (groupRingMap symmetry value).coeff (symmetry g) := by rw [hfixed]
    _ = value.coeff g := groupRingMap_coeff_image symmetry value g



theorem coeff_inv_eq_of_adjoint_fixed
    (value : RationalGroupRing G)
    (hfixed : RationalGroupRing.adjoint value = value) (g : G) :
    value.coeff g⁻¹ = value.coeff g := by
  simpa only [RationalGroupRing.adjoint_apply] using
    congrArg (fun x : RationalGroupRing G => x.coeff g) hfixed








theorem groupRing_eq_of_invariant_orbit_coefficients
    [DecidableEq G] {κ : Type v} {σ : Type w}
    (left right : RationalGroupRing G)
    (representative : κ → G) (symmetry : σ → G ≃* G)
    (hleft_symmetry : ∀ s, groupRingMap (symmetry s) left = left)
    (hright_symmetry : ∀ s, groupRingMap (symmetry s) right = right)
    (hleft_adjoint : RationalGroupRing.adjoint left = left)
    (hright_adjoint : RationalGroupRing.adjoint right = right)
    (hcover : ∀ g ∈ left.coeff.support ∪ right.coeff.support,
      ∃ k s, g = symmetry s (representative k) ∨
        g = (symmetry s (representative k))⁻¹)
    (hrepresentative : ∀ k,
      left.coeff (representative k) = right.coeff (representative k)) :
    left = right := by
  apply groupRing_eq_of_coeff_eq_on_support left right
  intro g hg
  obtain ⟨k, s, heq | heq⟩ := hcover g hg
  · subst g
    rw [coeff_image_eq_of_groupRingMap_fixed
      (symmetry s) left (hleft_symmetry s),
      coeff_image_eq_of_groupRingMap_fixed
        (symmetry s) right (hright_symmetry s)]
    exact hrepresentative k
  · subst g
    rw [coeff_inv_eq_of_adjoint_fixed left hleft_adjoint,
      coeff_inv_eq_of_adjoint_fixed right hright_adjoint,
      coeff_image_eq_of_groupRingMap_fixed
        (symmetry s) left (hleft_symmetry s),
      coeff_image_eq_of_groupRingMap_fixed
        (symmetry s) right (hright_symmetry s)]
    exact hrepresentative k

end ConnesRigidity.AffineSymplecticOrbitCertificate

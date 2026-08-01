


import ConnesRigidity.GroupRingCertificateAlgebra










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

universe u

variable {G : Type u} [Group G]

noncomputable local instance : DecidableEq G := Classical.decEq G


noncomputable def groupRingMap (e : G ≃* G) :
    RationalGroupRing G →+* RationalGroupRing G :=
  (MonoidAlgebra.mapDomainRingEquiv ℚ e).toRingHom

@[simp]
theorem groupRingMap_single (e : G ≃* G) (g : G) (r : ℚ) :
    groupRingMap e (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (e g) r := by
  exact MonoidAlgebra.mapDomainRingEquiv_single e r g

@[simp]
theorem groupRingMap_smul (e : G ≃* G) (r : ℚ)
    (a : RationalGroupRing G) :
    groupRingMap e (r • a) = r • groupRingMap e a := by
  change MonoidAlgebra.mapDomain (e : G → G) (r • a) =
    r • MonoidAlgebra.mapDomain (e : G → G) a
  exact MonoidAlgebra.mapDomain_smul _ _ _



@[simp]
theorem groupRingMap_comp (e f : G ≃* G) (a : RationalGroupRing G) :
    groupRingMap e (groupRingMap f a) = groupRingMap (f.trans e) a := by
  classical
  induction a using MonoidAlgebra.induction with
  | zero => simp
  | single_add g r a _hg _hr ih =>
      simp [ih]



@[simp]
theorem groupRingMap_adjoint (e : G ≃* G) (a : RationalGroupRing G) :
    groupRingMap e (RationalGroupRing.adjoint a) =
      RationalGroupRing.adjoint (groupRingMap e a) := by
  classical
  induction a using MonoidAlgebra.induction with
  | zero => simp
  | single_add g r a _hg _hr ih =>
      simp [ih, map_inv]

@[simp]
theorem groupRingMap_difference (e : G ≃* G) (g : G) :
    groupRingMap e (RationalGroupRing.difference g) =
      RationalGroupRing.difference (e g) := by
  simp [RationalGroupRing.difference]


theorem groupRingMap_customaryLaplacian_image
    (e : G ≃* G) (K : Finset G) :
    groupRingMap e (RationalGroupRing.customaryLaplacian K) =
      RationalGroupRing.customaryLaplacian (K.image e) := by
  classical
  simp only [RationalGroupRing.customaryLaplacian, map_sum,
    groupRingMap_difference]
  rw [Finset.sum_image]
  intro g _ h _ hgh
  exact e.injective hgh



theorem groupRingMap_customaryLaplacian_of_image_eq
    (e : G ≃* G) (K : Finset G) (hK : K.image e = K) :
    groupRingMap e (RationalGroupRing.customaryLaplacian K) =
      RationalGroupRing.customaryLaplacian K := by
  rw [groupRingMap_customaryLaplacian_image, hK]


theorem groupRingMap_laplacian_image
    (e : G ≃* G) (K : Finset G) :
    groupRingMap e (RationalGroupRing.laplacian K) =
      RationalGroupRing.laplacian (K.image e) := by
  classical
  simp only [RationalGroupRing.laplacian, map_sum, map_mul,
    groupRingMap_adjoint, groupRingMap_difference]
  rw [Finset.sum_image]
  intro g _ h _ hgh
  exact e.injective hgh



theorem groupRingMap_laplacian_of_image_eq
    (e : G ≃* G) (K : Finset G) (hK : K.image e = K) :
    groupRingMap e (RationalGroupRing.laplacian K) =
      RationalGroupRing.laplacian K := by
  rw [groupRingMap_laplacian_image, hK]



@[simp]
theorem groupRingMap_adjoint_mul_self (e : G ≃* G)
    (a : RationalGroupRing G) :
    groupRingMap e (RationalGroupRing.adjoint a * a) =
      RationalGroupRing.adjoint (groupRingMap e a) * groupRingMap e a := by
  simp

end ConnesRigidity.AffineSymplecticOrbitCertificate




import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
import ConnesRigidity.PropertyTExactCertificateOrbitPairOrbitMembership












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



noncomputable def orbitCoverageCoefficientKey (gram : Fin 2256) : Fin 995 := by
  have hindex : gram.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  have hfields := orbitGramRepresentativeFields_valid gram.val hindex
  have hfield :
      gramOrbitCoefficientOrbit gram.val =
        orbitEntry (gramOrbitData[gram.val]) 2 := by
    simp [gramOrbitCoefficientOrbit, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hindex]
  have hbounds : 0 ≤ gramOrbitCoefficientOrbit gram.val ∧
      gramOrbitCoefficientOrbit gram.val < (995 : Int) := by
    rw [hfield]
    simpa [coefficientRepresentativeData_size] using hfields.2.2.2.1
  exact ⟨(gramOrbitCoefficientOrbit gram.val).toNat,
    (Int.toNat_lt hbounds.1).mpr hbounds.2⟩



theorem orbitGramPair_coefficientRepresentative_coverage_of_transport
    (htransport : ∀ gram : Fin 2256,
      coefficientRepresentativeElement
          (gramOrbitCoefficientOrbit gram.val).toNat ∈
        MulAction.orbit OrbitSignedSymmetry
          ((orbitBasis (orbitGramRepresentative gram).1)⁻¹ *
            orbitBasis (orbitGramRepresentative gram).2))
    (left right : Fin 425) :
    ∃ orbit : Fin 995, ∃ symmetry : Fin 64,
      (orbitBasis left)⁻¹ * orbitBasis right =
        orbitSymmetry symmetry (coefficientRepresentativeElement orbit.val) ∨
      (orbitBasis left)⁻¹ * orbitBasis right =
        (orbitSymmetry symmetry
          (coefficientRepresentativeElement orbit.val))⁻¹ := by
  let gram := orbitPairKey left right
  let representative := orbitGramRepresentative gram
  let coefficient := orbitCoverageCoefficientKey gram
  obtain ⟨pairSymmetry, hpair⟩ :=
    MulAction.mem_orbit_iff.mp
      (orbitPair_mem_representative_orbit left right)
  have hproduct := signedPairProduct_equivariant orbitBasis
    orbitSymmetry_basis_action pairSymmetry representative
  change pairSymmetry • representative = (left, right) at hpair
  rw [hpair] at hproduct
  obtain ⟨coefficientSymmetry, hcoefficient⟩ :=
    MulAction.mem_orbit_iff.mp (htransport gram)
  let signed : OrbitSignedSymmetry := pairSymmetry * coefficientSymmetry⁻¹
  have hsigned :
      (orbitBasis left)⁻¹ * orbitBasis right =
        signed • coefficientRepresentativeElement coefficient.val := by
    change (orbitBasis left)⁻¹ * orbitBasis right =
      (pairSymmetry * coefficientSymmetry⁻¹) •
        coefficientRepresentativeElement coefficient.val
    change (orbitBasis left)⁻¹ * orbitBasis right =
      (pairSymmetry * coefficientSymmetry⁻¹) •
        coefficientRepresentativeElement
          (gramOrbitCoefficientOrbit gram.val).toNat
    rw [mul_smul, ← hcoefficient, inv_smul_smul]
    exact hproduct
  refine ⟨coefficient, signed.1.index, ?_⟩
  by_cases hparity : signed.2.toAdd = 0
  · left
    simpa [signedGroupAction_apply, hparity] using hsigned
  · right
    simpa [signedGroupAction_apply, hparity] using hsigned

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

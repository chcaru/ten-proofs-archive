
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientOrbitDisjointness
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalCodeSorted
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalLexProof

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem coefficientRepresentative_orbits_disjoint
    (first second : Fin 995)
    (horbit : coefficientRepresentativeElement first.val ∈
      MulAction.orbit OrbitSignedSymmetry
        (coefficientRepresentativeElement second.val)) :
    first = second := by
  obtain ⟨symmetry, hsymmetry⟩ := MulAction.mem_orbit_iff.mp horbit
  have hcanonical :
      coefficientCanonicalCoordinates
          (coefficientRepresentativeElement first.val) =
        coefficientCanonicalCoordinates
          (coefficientRepresentativeElement second.val) := by
    rw [← hsymmetry, coefficientCanonicalCoordinates_smul]
  obtain ⟨firstRow, hfirstCanonical, hfirstCode⟩ :=
    coefficientCanonicalCoordinates_representative first
  obtain ⟨secondRow, hsecondCanonical, hsecondCode⟩ :=
    coefficientCanonicalCoordinates_representative second
  have hrows :
      firstRow = secondRow := by
    simpa using congrArg List.reverse
      (hfirstCanonical.symm.trans
        (hcanonical.trans hsecondCanonical))
  apply coefficientCanonicalCodeRow_injective first second
  exact hfirstCode.symm.trans
    ((congrArg targetCoordinateCode hrows).trans hsecondCode)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate


import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientIncidenceConcrete
import ConnesRigidity.PropertyTExactCertificateOrbitPairOrbitSaturation
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerCoefficientCard

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000

theorem orbitGramPairFiberCount_eq_checked_of_witnesses
    (hbucket : ∀ (gram : Fin 2256) (pair : Fin 425 × Fin 425),
      orbitPairKey pair.1 pair.2 = gram ↔
        pair ∈ MulAction.orbit OrbitSignedSymmetry
          (orbitGramRepresentative gram))
    (htransport : ∀ gram : Fin 2256,
      coefficientRepresentativeElement
          (orbitGramCoefficientKey gram).val ∈
        MulAction.orbit OrbitSignedSymmetry
          ((orbitBasis (orbitGramRepresentative gram).1)⁻¹ *
            orbitBasis (orbitGramRepresentative gram).2))
    (hcoefficientCard : ∀ coefficient : Fin 995,
      Fintype.card (MulAction.orbit OrbitSignedSymmetry
        (coefficientRepresentativeElement coefficient.val)) =
          (dataEntry coefficientOrbitSizeData coefficient.val 0).toNat)
    (hdisjoint : ∀ first second : Fin 995,
      coefficientRepresentativeElement first.val ∈
        MulAction.orbit OrbitSignedSymmetry
          (coefficientRepresentativeElement second.val) →
      first = second)
    (coefficient : Fin 995) (gram : Fin 2256) :
    gramPairFiberCount orbitBasis orbitPairKey gram
        (coefficientRepresentativeElement coefficient.val) =
      if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
      then (gramOrbitIncidence gram.val).toNat else 0 := by
  exact orbitGramRepresentative_fibers_of_orbits
    orbitPairKey orbitGramCoefficientKey orbitGramRepresentative
    orbitGramCoefficientKey_cast hbucket
    (signedPairProduct_equivariant orbitBasis orbitSymmetry_basis_action)
    htransport
    (fun gram => orbitGramRepresentative_fiber_incidence_of_coefficient_card
      orbitPairKey hbucket htransport hcoefficientCard gram)
    hdisjoint coefficient gram

theorem orbitGramPairFiberCount_eq_checked_of_transport_and_disjoint
    (htransport : ∀ gram : Fin 2256,
      coefficientRepresentativeElement
          (orbitGramCoefficientKey gram).val ∈
        MulAction.orbit OrbitSignedSymmetry
          ((orbitBasis (orbitGramRepresentative gram).1)⁻¹ *
            orbitBasis (orbitGramRepresentative gram).2))
    (hdisjoint : ∀ first second : Fin 995,
      coefficientRepresentativeElement first.val ∈
        MulAction.orbit OrbitSignedSymmetry
          (coefficientRepresentativeElement second.val) →
      first = second)
    (coefficient : Fin 995) (gram : Fin 2256) :
    gramPairFiberCount orbitBasis orbitPairKey gram
        (coefficientRepresentativeElement coefficient.val) =
      if gramOrbitCoefficientOrbit gram.val = (coefficient.val : Int)
      then (gramOrbitIncidence gram.val).toNat else 0 := by
  exact orbitGramPairFiberCount_eq_checked_of_witnesses
    orbitPair_bucket_iff htransport
    orbitCoefficientRepresentative_orbit_card hdisjoint coefficient gram

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

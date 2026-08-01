


import ConnesRigidity.PropertyTExactCertificateOrbitTargetFastValidation
import ConnesRigidity.PropertyTExactCertificateOrbitTargetIndexFastValidation
import ConnesRigidity.PropertyTExactCertificateOrbitTargetProductFastValidation









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0



theorem orbitTargetStreamingCheck_valid :
    orbitTargetStreamingCheck = true := by
  simp only [orbitTargetStreamingCheck, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]
  obtain ⟨hproducts, hproductIndices, hrepresentatives,
    hrepresentativeIndices, hcoefficientRepresentatives,
    htargetWitnesses⟩ := orbitTargetStreamingSizes_valid_fast
  exact ⟨hproducts, hproductIndices, hrepresentatives,
    hrepresentativeIndices, hcoefficientRepresentatives,
    htargetWitnesses, orbitTargetGeneratorRowsSymplecticCheck_valid_fast,
    orbitTargetProductRecordsCheck_valid_fast,
    orbitTargetProductInverseCheck_valid,
    orbitTargetRepresentativeInverseCheck_valid,
    orbitTargetProductGroupsCheck_valid,
    orbitTargetRepresentativeRowsCheck_valid_fast⟩

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

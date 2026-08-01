
import ConnesRigidity.PropertyTExactCertificateOrbitTargetWitness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitTargetProductInverseCheck_valid :
    orbitTargetProductInverseCheck 0 targetGeneratorProductRowIndexData = true := by
  unfold orbitTargetProductInverseCheck targetGeneratorProductRowIndexData
    targetGeneratorProductRowData
  decide +kernel

theorem orbitTargetRepresentativeInverseCheck_valid :
    orbitTargetRepresentativeInverseCheck 0 targetRepresentativeCodeIndexData = true := by
  unfold orbitTargetRepresentativeInverseCheck targetRepresentativeCodeIndexData
    targetRepresentativeCodeSortedData
  decide +kernel

theorem orbitTargetProductGroupsCheck_valid :
    orbitTargetProductGroupsCheck (-1) 0 targetGeneratorProductGroupData
      targetGeneratorProductRowData = true := by
  unfold orbitTargetProductGroupsCheck targetGroupCheck targetConsumeCode
    targetGeneratorProductGroupData targetGeneratorProductRowData
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

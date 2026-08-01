


import ConnesRigidity.PropertyTExactCertificateOrbitTargetWitness
import ConnesRigidity.PropertyTExactCertificateOrbitGeneratorTransport








namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


theorem orbitTargetStreamingSizes_valid_fast :
    targetGeneratorProductRowData.length = 576 ∧
      targetGeneratorProductRowIndexData.length = 576 ∧
      targetRepresentativeCodeSortedData.length = 995 ∧
      targetRepresentativeCodeIndexData.length = 995 ∧
      coefficientRepresentativeData.size = 995 ∧
      coefficientTargetWitnessData.size = 995 := by
  unfold targetGeneratorProductRowData targetGeneratorProductRowIndexData
    targetRepresentativeCodeSortedData targetRepresentativeCodeIndexData
    coefficientRepresentativeData coefficientTargetWitnessData
  decide +kernel


theorem orbitTargetGeneratorRowsSymplecticCheck_valid_fast :
    generatorRowsSymplecticCheck = true :=
  generatorRowsSymplecticCheck_valid


theorem orbitTargetProductRecordsCheck_valid_fast :
    orbitTargetProductRecordsCheck 0 targetGeneratorProductRowData = true := by
  unfold orbitTargetProductRecordsCheck orbitTargetProductRecordCheck
    orbitTargetProductRecordCoordinates targetCoordinateBounds isSymplecticRow
    rawProductCheck targetCoordinateCode targetGeneratorProductRowData
    targetGeneratorProductRowIndexData generatorData
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

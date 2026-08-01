


import ConnesRigidity.PropertyTExactCertificateOrbitTargetWitness








namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitTargetRepresentativeRowsCheck_valid_fast :
    orbitTargetRepresentativeRowsCheck (-1) 0
      targetRepresentativeCodeSortedData
      targetGeneratorProductGroupData = true := by
  unfold orbitTargetRepresentativeRowsCheck orbitTargetRepresentativeRecordCheck
    orbitTargetSeekProductGroup targetSeekGroup targetCoordinateBounds
    isSymplecticRow targetCoordinateCode targetRepresentativeCodeSortedData
    targetRepresentativeCodeIndexData targetGeneratorProductGroupData
    coefficientRepresentativeData coefficientTargetWitnessData basisData generatorData
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

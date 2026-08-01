
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedRow

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.setOption false

set_option maxHeartbeats 64000000 in

theorem coefficientCanonicalPackedWitnessBatch09 :
    coefficientCanonicalPackedWitnessRowsCheck canonicalPackedActionData
      ((canonicalPackedWitnessData.drop 900).take 100) = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate

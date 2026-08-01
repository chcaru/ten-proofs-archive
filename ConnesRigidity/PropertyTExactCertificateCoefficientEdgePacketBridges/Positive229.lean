


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive229
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_229 :
    coefficientPositivePacketTerms229 =
      (positiveEdgeTerms.drop 131904).take 576 := by
  unfold coefficientPositivePacketTerms229 coefficientPositivePacketRows229
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

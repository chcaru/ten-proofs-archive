


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive224
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_224 :
    coefficientPositivePacketTerms224 =
      (positiveEdgeTerms.drop 129024).take 576 := by
  unfold coefficientPositivePacketTerms224 coefficientPositivePacketRows224
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive231
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_231 :
    coefficientPositivePacketTerms231 =
      (positiveEdgeTerms.drop 133056).take 576 := by
  unfold coefficientPositivePacketTerms231 coefficientPositivePacketRows231
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

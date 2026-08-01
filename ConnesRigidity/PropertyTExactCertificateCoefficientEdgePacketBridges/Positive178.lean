


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive178
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_178 :
    coefficientPositivePacketTerms178 =
      (positiveEdgeTerms.drop 102528).take 576 := by
  unfold coefficientPositivePacketTerms178 coefficientPositivePacketRows178
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

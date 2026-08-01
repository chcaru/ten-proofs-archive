


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive183
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_183 :
    coefficientPositivePacketTerms183 =
      (positiveEdgeTerms.drop 105408).take 576 := by
  unfold coefficientPositivePacketTerms183 coefficientPositivePacketRows183
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

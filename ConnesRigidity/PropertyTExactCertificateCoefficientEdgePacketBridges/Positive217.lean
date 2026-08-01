


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive217
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_217 :
    coefficientPositivePacketTerms217 =
      (positiveEdgeTerms.drop 124992).take 576 := by
  unfold coefficientPositivePacketTerms217 coefficientPositivePacketRows217
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

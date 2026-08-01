


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive105
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_105 :
    coefficientPositivePacketTerms105 =
      (positiveEdgeTerms.drop 60480).take 576 := by
  unfold coefficientPositivePacketTerms105 coefficientPositivePacketRows105
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive132
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_132 :
    coefficientPositivePacketTerms132 =
      (positiveEdgeTerms.drop 76032).take 576 := by
  unfold coefficientPositivePacketTerms132 coefficientPositivePacketRows132
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

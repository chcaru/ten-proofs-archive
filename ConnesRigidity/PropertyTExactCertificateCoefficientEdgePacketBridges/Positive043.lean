


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive043
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_043 :
    coefficientPositivePacketTerms043 =
      (positiveEdgeTerms.drop 24768).take 576 := by
  unfold coefficientPositivePacketTerms043 coefficientPositivePacketRows043
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

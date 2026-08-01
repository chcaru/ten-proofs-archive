


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive236
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_236 :
    coefficientPositivePacketTerms236 =
      (positiveEdgeTerms.drop 135936).take 576 := by
  unfold coefficientPositivePacketTerms236 coefficientPositivePacketRows236
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

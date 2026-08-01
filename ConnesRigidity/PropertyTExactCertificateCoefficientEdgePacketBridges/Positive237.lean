


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive237
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_237 :
    coefficientPositivePacketTerms237 =
      (positiveEdgeTerms.drop 136512).take 576 := by
  unfold coefficientPositivePacketTerms237 coefficientPositivePacketRows237
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

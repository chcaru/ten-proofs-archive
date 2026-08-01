


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive061
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_061 :
    coefficientPositivePacketTerms061 =
      (positiveEdgeTerms.drop 35136).take 576 := by
  unfold coefficientPositivePacketTerms061 coefficientPositivePacketRows061
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

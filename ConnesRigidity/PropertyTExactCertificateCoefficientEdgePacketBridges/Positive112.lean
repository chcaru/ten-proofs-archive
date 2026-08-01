


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive112
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_112 :
    coefficientPositivePacketTerms112 =
      (positiveEdgeTerms.drop 64512).take 576 := by
  unfold coefficientPositivePacketTerms112 coefficientPositivePacketRows112
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

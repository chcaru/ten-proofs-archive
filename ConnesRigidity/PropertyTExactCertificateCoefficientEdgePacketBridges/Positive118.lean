


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive118
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_118 :
    coefficientPositivePacketTerms118 =
      (positiveEdgeTerms.drop 67968).take 576 := by
  unfold coefficientPositivePacketTerms118 coefficientPositivePacketRows118
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

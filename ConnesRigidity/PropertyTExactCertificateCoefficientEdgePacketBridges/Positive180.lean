


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive180
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_180 :
    coefficientPositivePacketTerms180 =
      (positiveEdgeTerms.drop 103680).take 576 := by
  unfold coefficientPositivePacketTerms180 coefficientPositivePacketRows180
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

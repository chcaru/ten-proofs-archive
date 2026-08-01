


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive085
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_085 :
    coefficientPositivePacketTerms085 =
      (positiveEdgeTerms.drop 48960).take 576 := by
  unfold coefficientPositivePacketTerms085 coefficientPositivePacketRows085
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive166
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_166 :
    coefficientPositivePacketTerms166 =
      (positiveEdgeTerms.drop 95616).take 576 := by
  unfold coefficientPositivePacketTerms166 coefficientPositivePacketRows166
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

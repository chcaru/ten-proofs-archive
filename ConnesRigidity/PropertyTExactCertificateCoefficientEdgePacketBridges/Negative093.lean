


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative093
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_093 :
    coefficientNegativePacketTerms093 =
      (negativeEdgeTerms.drop 47616).take 512 := by
  unfold coefficientNegativePacketTerms093 coefficientNegativePacketRows093
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

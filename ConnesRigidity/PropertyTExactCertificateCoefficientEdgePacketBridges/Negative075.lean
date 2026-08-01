


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative075
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_075 :
    coefficientNegativePacketTerms075 =
      (negativeEdgeTerms.drop 38400).take 512 := by
  unfold coefficientNegativePacketTerms075 coefficientNegativePacketRows075
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative068
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_068 :
    coefficientNegativePacketTerms068 =
      (negativeEdgeTerms.drop 34816).take 512 := by
  unfold coefficientNegativePacketTerms068 coefficientNegativePacketRows068
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

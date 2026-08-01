


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative143
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_143 :
    coefficientNegativePacketTerms143 =
      (negativeEdgeTerms.drop 73216).take 512 := by
  unfold coefficientNegativePacketTerms143 coefficientNegativePacketRows143
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

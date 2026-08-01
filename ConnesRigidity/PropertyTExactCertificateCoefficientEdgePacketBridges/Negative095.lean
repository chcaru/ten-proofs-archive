


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative095
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_095 :
    coefficientNegativePacketTerms095 =
      (negativeEdgeTerms.drop 48640).take 512 := by
  unfold coefficientNegativePacketTerms095 coefficientNegativePacketRows095
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

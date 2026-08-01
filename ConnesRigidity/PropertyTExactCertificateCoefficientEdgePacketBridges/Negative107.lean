


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative107
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_107 :
    coefficientNegativePacketTerms107 =
      (negativeEdgeTerms.drop 54784).take 512 := by
  unfold coefficientNegativePacketTerms107 coefficientNegativePacketRows107
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative023
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_023 :
    coefficientNegativePacketTerms023 =
      (negativeEdgeTerms.drop 11776).take 512 := by
  unfold coefficientNegativePacketTerms023 coefficientNegativePacketRows023
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

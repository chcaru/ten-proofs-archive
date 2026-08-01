


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative103
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_103 :
    coefficientNegativePacketTerms103 =
      (negativeEdgeTerms.drop 52736).take 512 := by
  unfold coefficientNegativePacketTerms103 coefficientNegativePacketRows103
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative002
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_002 :
    coefficientNegativePacketTerms002 =
      (negativeEdgeTerms.drop 1024).take 512 := by
  unfold coefficientNegativePacketTerms002 coefficientNegativePacketRows002
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

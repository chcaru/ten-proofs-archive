


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative058
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_058 :
    coefficientNegativePacketTerms058 =
      (negativeEdgeTerms.drop 29696).take 512 := by
  unfold coefficientNegativePacketTerms058 coefficientNegativePacketRows058
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

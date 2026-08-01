


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative018
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_018 :
    coefficientNegativePacketTerms018 =
      (negativeEdgeTerms.drop 9216).take 512 := by
  unfold coefficientNegativePacketTerms018 coefficientNegativePacketRows018
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

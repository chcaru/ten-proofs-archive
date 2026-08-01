


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative015
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_015 :
    coefficientNegativePacketTerms015 =
      (negativeEdgeTerms.drop 7680).take 512 := by
  unfold coefficientNegativePacketTerms015 coefficientNegativePacketRows015
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative032
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_032 :
    coefficientNegativePacketTerms032 =
      (negativeEdgeTerms.drop 16384).take 512 := by
  unfold coefficientNegativePacketTerms032 coefficientNegativePacketRows032
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

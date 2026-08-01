


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative026
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_026 :
    coefficientNegativePacketTerms026 =
      (negativeEdgeTerms.drop 13312).take 512 := by
  unfold coefficientNegativePacketTerms026 coefficientNegativePacketRows026
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative022
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_022 :
    coefficientNegativePacketTerms022 =
      (negativeEdgeTerms.drop 11264).take 512 := by
  unfold coefficientNegativePacketTerms022 coefficientNegativePacketRows022
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

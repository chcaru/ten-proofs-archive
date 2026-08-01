


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative112
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_112 :
    coefficientNegativePacketTerms112 =
      (negativeEdgeTerms.drop 57344).take 512 := by
  unfold coefficientNegativePacketTerms112 coefficientNegativePacketRows112
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

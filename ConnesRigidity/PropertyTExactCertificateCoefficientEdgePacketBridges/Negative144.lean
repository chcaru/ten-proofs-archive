


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative144
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_144 :
    coefficientNegativePacketTerms144 =
      (negativeEdgeTerms.drop 73728).take 512 := by
  unfold coefficientNegativePacketTerms144 coefficientNegativePacketRows144
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

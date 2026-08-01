


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative121
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_121 :
    coefficientNegativePacketTerms121 =
      (negativeEdgeTerms.drop 61952).take 512 := by
  unfold coefficientNegativePacketTerms121 coefficientNegativePacketRows121
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

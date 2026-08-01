


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative000
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_000 :
    coefficientNegativePacketTerms000 =
      (negativeEdgeTerms.drop 0).take 512 := by
  unfold coefficientNegativePacketTerms000 coefficientNegativePacketRows000
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

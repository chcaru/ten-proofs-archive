


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative114
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_114 :
    coefficientNegativePacketTerms114 =
      (negativeEdgeTerms.drop 58368).take 512 := by
  unfold coefficientNegativePacketTerms114 coefficientNegativePacketRows114
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

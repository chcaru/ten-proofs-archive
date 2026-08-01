


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative012
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_012 :
    coefficientNegativePacketTerms012 =
      (negativeEdgeTerms.drop 6144).take 512 := by
  unfold coefficientNegativePacketTerms012 coefficientNegativePacketRows012
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

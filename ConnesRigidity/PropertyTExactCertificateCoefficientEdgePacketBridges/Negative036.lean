


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative036
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_036 :
    coefficientNegativePacketTerms036 =
      (negativeEdgeTerms.drop 18432).take 512 := by
  unfold coefficientNegativePacketTerms036 coefficientNegativePacketRows036
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

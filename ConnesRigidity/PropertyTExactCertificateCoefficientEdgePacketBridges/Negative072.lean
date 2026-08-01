


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative072
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_072 :
    coefficientNegativePacketTerms072 =
      (negativeEdgeTerms.drop 36864).take 512 := by
  unfold coefficientNegativePacketTerms072 coefficientNegativePacketRows072
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

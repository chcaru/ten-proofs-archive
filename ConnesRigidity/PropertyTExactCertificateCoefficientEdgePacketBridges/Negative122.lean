
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative122
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_122 :
    coefficientNegativePacketTerms122 =
      (negativeEdgeTerms.drop 62464).take 512 := by
  unfold coefficientNegativePacketTerms122 coefficientNegativePacketRows122
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

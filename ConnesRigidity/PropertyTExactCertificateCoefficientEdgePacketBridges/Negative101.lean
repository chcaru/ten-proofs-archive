
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative101
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_101 :
    coefficientNegativePacketTerms101 =
      (negativeEdgeTerms.drop 51712).take 512 := by
  unfold coefficientNegativePacketTerms101 coefficientNegativePacketRows101
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative102
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_102 :
    coefficientNegativePacketTerms102 =
      (negativeEdgeTerms.drop 52224).take 512 := by
  unfold coefficientNegativePacketTerms102 coefficientNegativePacketRows102
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

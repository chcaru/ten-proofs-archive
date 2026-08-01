
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative009
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_009 :
    coefficientNegativePacketTerms009 =
      (negativeEdgeTerms.drop 4608).take 512 := by
  unfold coefficientNegativePacketTerms009 coefficientNegativePacketRows009
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

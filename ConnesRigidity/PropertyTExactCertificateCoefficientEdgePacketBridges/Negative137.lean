
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative137
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_137 :
    coefficientNegativePacketTerms137 =
      (negativeEdgeTerms.drop 70144).take 512 := by
  unfold coefficientNegativePacketTerms137 coefficientNegativePacketRows137
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

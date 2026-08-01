
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative134
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_134 :
    coefficientNegativePacketTerms134 =
      (negativeEdgeTerms.drop 68608).take 512 := by
  unfold coefficientNegativePacketTerms134 coefficientNegativePacketRows134
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

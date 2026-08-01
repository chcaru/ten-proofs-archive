
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative149
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_149 :
    coefficientNegativePacketTerms149 =
      (negativeEdgeTerms.drop 76288).take 512 := by
  unfold coefficientNegativePacketTerms149 coefficientNegativePacketRows149
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

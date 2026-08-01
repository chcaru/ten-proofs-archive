
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative115
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_115 :
    coefficientNegativePacketTerms115 =
      (negativeEdgeTerms.drop 58880).take 512 := by
  unfold coefficientNegativePacketTerms115 coefficientNegativePacketRows115
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative067
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_067 :
    coefficientNegativePacketTerms067 =
      (negativeEdgeTerms.drop 34304).take 512 := by
  unfold coefficientNegativePacketTerms067 coefficientNegativePacketRows067
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative124
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_124 :
    coefficientNegativePacketTerms124 =
      (negativeEdgeTerms.drop 63488).take 512 := by
  unfold coefficientNegativePacketTerms124 coefficientNegativePacketRows124
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

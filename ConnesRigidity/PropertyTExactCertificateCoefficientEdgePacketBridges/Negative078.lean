
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative078
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_078 :
    coefficientNegativePacketTerms078 =
      (negativeEdgeTerms.drop 39936).take 512 := by
  unfold coefficientNegativePacketTerms078 coefficientNegativePacketRows078
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

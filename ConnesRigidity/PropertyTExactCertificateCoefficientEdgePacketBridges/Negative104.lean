
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative104
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_104 :
    coefficientNegativePacketTerms104 =
      (negativeEdgeTerms.drop 53248).take 512 := by
  unfold coefficientNegativePacketTerms104 coefficientNegativePacketRows104
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

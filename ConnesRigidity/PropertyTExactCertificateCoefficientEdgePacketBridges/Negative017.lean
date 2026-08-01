
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative017
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_017 :
    coefficientNegativePacketTerms017 =
      (negativeEdgeTerms.drop 8704).take 512 := by
  unfold coefficientNegativePacketTerms017 coefficientNegativePacketRows017
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

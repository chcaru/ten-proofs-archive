
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative038
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_038 :
    coefficientNegativePacketTerms038 =
      (negativeEdgeTerms.drop 19456).take 512 := by
  unfold coefficientNegativePacketTerms038 coefficientNegativePacketRows038
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

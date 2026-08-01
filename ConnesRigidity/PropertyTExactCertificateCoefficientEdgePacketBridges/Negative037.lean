
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative037
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_037 :
    coefficientNegativePacketTerms037 =
      (negativeEdgeTerms.drop 18944).take 512 := by
  unfold coefficientNegativePacketTerms037 coefficientNegativePacketRows037
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

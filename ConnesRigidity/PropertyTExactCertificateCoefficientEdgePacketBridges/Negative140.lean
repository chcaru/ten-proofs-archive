
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative140
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_140 :
    coefficientNegativePacketTerms140 =
      (negativeEdgeTerms.drop 71680).take 512 := by
  unfold coefficientNegativePacketTerms140 coefficientNegativePacketRows140
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

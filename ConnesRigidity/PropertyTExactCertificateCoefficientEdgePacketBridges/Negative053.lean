
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative053
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_053 :
    coefficientNegativePacketTerms053 =
      (negativeEdgeTerms.drop 27136).take 512 := by
  unfold coefficientNegativePacketTerms053 coefficientNegativePacketRows053
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

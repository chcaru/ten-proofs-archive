
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive106
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_106 :
    coefficientPositivePacketTerms106 =
      (positiveEdgeTerms.drop 61056).take 576 := by
  unfold coefficientPositivePacketTerms106 coefficientPositivePacketRows106
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

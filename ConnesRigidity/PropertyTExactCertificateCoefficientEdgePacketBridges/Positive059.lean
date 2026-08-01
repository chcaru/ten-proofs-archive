
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive059
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_059 :
    coefficientPositivePacketTerms059 =
      (positiveEdgeTerms.drop 33984).take 576 := by
  unfold coefficientPositivePacketTerms059 coefficientPositivePacketRows059
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

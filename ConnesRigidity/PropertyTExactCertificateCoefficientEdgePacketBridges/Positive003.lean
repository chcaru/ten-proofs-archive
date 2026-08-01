
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive003
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_003 :
    coefficientPositivePacketTerms003 =
      (positiveEdgeTerms.drop 1728).take 576 := by
  unfold coefficientPositivePacketTerms003 coefficientPositivePacketRows003
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
